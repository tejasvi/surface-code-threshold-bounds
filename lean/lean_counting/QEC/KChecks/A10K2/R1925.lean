import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7700 = true := by
  decide +kernel

theorem tot7700 : totK PA10K2 A10K2.t7700 = [0, 0, 214169341392, 567914053375, 638489665152, 1374360571048, 1616860003951, 534357282439, 41590655314, 0] := by
  decide +kernel

theorem rows7701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7701 = true := by
  decide +kernel

theorem tot7701 : totK PA10K2 A10K2.t7701 = [0, 0, 495750635694, 1787020499806, 1956982726471, 556404006559, 32846095359, 0, 0, 0] := by
  decide +kernel

theorem rows7702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7702 = true := by
  decide +kernel

theorem tot7702 : totK PA10K2 A10K2.t7702 = [0, 0, 125906897604, 1033798044370, 2083091007567, 1347276890096, 277538927365, 20340910120, 0, 0] := by
  decide +kernel

theorem rows7703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7703 = true := by
  decide +kernel

theorem tot7703 : totK PA10K2 A10K2.t7703 = [0, 0, 106417210075, 763167602535, 1922235727478, 1633608905262, 335254012148, 11427838733, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
