/*

    This file is part of the Maude 2 interpreter.

    Copyright 1997-2003 SRI International, Menlo Park, CA 94025, USA.

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.

*/

//
//	Code for handling importation.
//

void
PreModule::processImports()
{
  //
  //	Automatic imports.
  //
  FOR_EACH_CONST(i, ModuleDatabase::ImportMap, autoImports)
    {
      if (ImportModule* fm = getModule(i->first, *this))
	flatModule->addImport(fm, i->second, *this);
   }
  //
  //	Explicit imports.
  //
  int nrImports = imports.length();
  for (int i = 0; i < nrImports; i++)
    {
      Import import = imports[i];
      if (ImportModule* fm = makeModule(import.expr))
	{
	  Import import = imports[i];
	  ImportModule::ImportMode mode;
	  int code = import.mode.code();
	  LineNumber lineNumber(import.mode.lineNumber());
	  if (code == Token::encode("pr") || code == Token::encode("protecting"))
	    mode = ImportModule::PROTECTING;
	  else if (code == Token::encode("ex") || code == Token::encode("extending"))
	    mode = ImportModule::EXTENDING;
	  else if (code == Token::encode("inc") || code == Token::encode("including"))
	    mode = ImportModule::INCLUDING;
	  else if (code == Token::encode("us") || code == Token::encode("using"))
	    {
	      IssueWarning(lineNumber <<
			   ": importation mode " << QUOTE("using") <<
			   " not supported - treating it like " <<
			   QUOTE("including") << '.');
	      mode = ImportModule::INCLUDING;
	    }
	  flatModule->addImport(fm, mode, lineNumber);
	}
    }
  //
  //	House keeping.
  //
  interpreter.destructUnusedModules();
}

ImportModule*
PreModule::getModule(int name, const LineNumber& lineNumber)
{
  if (PreModule* m = interpreter.getModule(name))
    {
      if (ImportModule* fm = m->getFlatSignature())
	{
	  //
	  //	We might have had to build a parser for this
	  //	module in order to deal with local statements,
	  //	term hooks and identities.
	  //	We delete the parser since we don't
	  //	have any further use for it.
	  //
	  fm->economize();
	  if (fm->isBad())
	    {
	      IssueWarning(lineNumber << ": unable to use module " <<
			   QUOTE(m) << " due to unpatchable errors.");
	    }
	  else
	    return fm;
	}
      else
	{
	  IssueWarning(lineNumber <<
		       ": mutually recursive import of module " <<
		       QUOTE(m) << " ignored.");
	}
    }
  else
    {
      IssueWarning(lineNumber <<
		   ": module " << QUOTE(Token::name(name)) <<
		   " does not exist.");
    }
  return 0;
}

ImportModule*
PreModule::makeModule(const ModuleExpression* expr)
{
  switch (expr->getType())
    {
    case ModuleExpression::MODULE:
      {
	Token name = expr->getModuleName();
	if (ImportModule* fm = getModule(name.code(), name.lineNumber()))
	  return fm;
	break;
      }
    case ModuleExpression::RENAMING:
      {
	if (ImportModule* fm = makeModule(expr->getModule()))
	  return interpreter.makeRenamedCopy(fm, expr->getRenaming());
	break;
      }
    case ModuleExpression::SUMMATION:
      {
	const list<ModuleExpression*>& modules = expr->getModules();
	Vector<ImportModule*> fms;
	FOR_EACH_CONST(i, list<ModuleExpression*>, modules)
	  {
	    if (ImportModule* fm = makeModule(*i))
	      fms.append(fm);
	  }
	if (!fms.empty())
	  return interpreter.makeSummation(fms);
	break;
      }
    default:
      CantHappen("bad module expression");
    }
  return 0;
}