import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows84 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t84 = true := by
  decide +kernel

theorem tot84 : totK PA10K2 A10K2.t84 = [297392362862, 1141430960751, 1820886423566, 1216507963662, 235506096072, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows85 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t85 = true := by
  decide +kernel

theorem tot85 : totK PA10K2 A10K2.t85 = [292846243945, 1517203737973, 2266812478148, 925605110779, 75635660390, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows86 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t86 = true := by
  decide +kernel

theorem tot86 : totK PA10K2 A10K2.t86 = [0, 475328261166, 1902047771894, 2105594841232, 541666567541, 17951502659, 0, 0, 0, 0] := by
  decide +kernel

theorem rows87 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t87 = true := by
  decide +kernel

theorem tot87 : totK PA10K2 A10K2.t87 = [0, 580749706947, 1830450049870, 1735991529476, 591648578718, 62885083427, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
