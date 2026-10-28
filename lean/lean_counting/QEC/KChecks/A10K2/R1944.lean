import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7776 = true := by
  decide +kernel

theorem tot7776 : totK PA10K2 A10K2.t7776 = [0, 0, 504368969528, 1919985751142, 2120455700436, 587914929888, 19836780544, 0, 0, 0] := by
  decide +kernel

theorem rows7777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7777 = true := by
  decide +kernel

theorem tot7777 : totK PA10K2 A10K2.t7777 = [0, 539846047986, 1761937758639, 1640417224271, 634783513366, 246150853290, 37646807062, 0, 0, 0] := by
  decide +kernel

theorem rows7778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7778 = true := by
  decide +kernel

theorem tot7778 : totK PA10K2 A10K2.t7778 = [0, 219708306998, 1301972863804, 2287998054488, 1099530458915, 114847994394, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7779 = true := by
  decide +kernel

theorem tot7779 : totK PA10K2 A10K2.t7779 = [0, 109458229214, 635658893944, 1705309528013, 1744121571914, 485039259989, 30831673886, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
