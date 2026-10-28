import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t336 = true := by
  decide +kernel

theorem tot336 : totK PA10K2 A10K2.t336 = [0, 0, 464522314952, 1659217826465, 1904908678277, 695058337232, 64246330671, 0, 0, 0] := by
  decide +kernel

theorem rows337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t337 = true := by
  decide +kernel

theorem tot337 : totK PA10K2 A10K2.t337 = [0, 0, 291183364528, 1515774238074, 2091061204356, 722308901535, 44556629621, 0, 0, 0] := by
  decide +kernel

theorem rows338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t338 = true := by
  decide +kernel

theorem tot338 : totK PA10K2 A10K2.t338 = [0, 0, 227476622735, 1040680580151, 1908366186877, 1220732924421, 187748010942, 6354482628, 0, 0] := by
  decide +kernel

theorem rows339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t339 = true := by
  decide +kernel

theorem tot339 : totK PA10K2 A10K2.t339 = [0, 0, 362761984072, 1697296419538, 2220556995840, 756089556180, 55332685257, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
