import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1016 = true := by
  decide +kernel

theorem tot1016 : totK PA10K2 A10K2.t1016 = [0, 0, 134809519436, 835765438796, 1865456928383, 1512562882309, 321237886174, 10751746851, 0, 0] := by
  decide +kernel

theorem rows1017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1017 = true := by
  decide +kernel

theorem tot1017 : totK PA10K2 A10K2.t1017 = [0, 0, 426811223662, 1793382687917, 1994783081479, 550688097865, 32877822373, 0, 0, 0] := by
  decide +kernel

theorem rows1018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1018 = true := by
  decide +kernel

theorem tot1018 : totK PA10K2 A10K2.t1018 = [0, 0, 190107525503, 1072813911770, 2043452694305, 1253449787118, 188667339871, 5885702948, 0, 0] := by
  decide +kernel

theorem rows1019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1019 = true := by
  decide +kernel

theorem tot1019 : totK PA10K2 A10K2.t1019 = [0, 0, 610145812838, 1954344447684, 1869596291062, 534443664557, 32470345011, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
