import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4632 = true := by
  decide +kernel

theorem tot4632 : totK PA10K2 A10K2.t4632 = [0, 0, 475553799053, 1725320095975, 2023553532858, 713284745332, 56084282801, 0, 0, 0] := by
  decide +kernel

theorem rows4633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4633 = true := by
  decide +kernel

theorem tot4633 : totK PA10K2 A10K2.t4633 = [0, 0, 497181656385, 1840050607706, 1894235324202, 519899615633, 31741948405, 0, 0, 0] := by
  decide +kernel

theorem rows4634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4634 = true := by
  decide +kernel

theorem tot4634 : totK PA10K2 A10K2.t4634 = [0, 0, 183742798465, 1147828359008, 2134014726525, 1261159923667, 214716543273, 7151180950, 0, 0] := by
  decide +kernel

theorem rows4635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4635 = true := by
  decide +kernel

theorem tot4635 : totK PA10K2 A10K2.t4635 = [0, 0, 429241339615, 1536173416870, 1951169622495, 841283985327, 83002309060, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
