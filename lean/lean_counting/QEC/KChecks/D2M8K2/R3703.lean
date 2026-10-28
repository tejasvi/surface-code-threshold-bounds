import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14812 = true := by
  decide +kernel

theorem tot14812 : totK PD2M8K2 D2M8K2.t14812 = [154328038265, 461535129351, 274290745927, 19963177022, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14813 = true := by
  decide +kernel

theorem tot14813 : totK PD2M8K2 D2M8K2.t14813 = [0, 229024809022, 500923710648, 161495275047, 7166294683, 0, 0, 0] := by
  decide +kernel

theorem rows14814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14814 = true := by
  decide +kernel

theorem tot14814 : totK PD2M8K2 D2M8K2.t14814 = [79494159424, 276070081822, 383409992413, 127814129146, 5883432551, 0, 0, 0] := by
  decide +kernel

theorem rows14815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14815 = true := by
  decide +kernel

theorem tot14815 : totK PD2M8K2 D2M8K2.t14815 = [172483855954, 463620446767, 256332877875, 23109284985, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
