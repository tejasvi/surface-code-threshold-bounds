import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14892 = true := by
  decide +kernel

theorem tot14892 : totK PD2M8K2 D2M8K2.t14892 = [0, 279263353221, 507256739777, 123340628425, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows14893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14893 = true := by
  decide +kernel

theorem tot14893 : totK PD2M8K2 D2M8K2.t14893 = [0, 185293791996, 484094163984, 208738578903, 8669917095, 0, 0, 0] := by
  decide +kernel

theorem rows14894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14894 = true := by
  decide +kernel

theorem tot14894 : totK PD2M8K2 D2M8K2.t14894 = [0, 175737509362, 473426714632, 226622222601, 14631128802, 0, 0, 0] := by
  decide +kernel

theorem rows14895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14895 = true := by
  decide +kernel

theorem tot14895 : totK PD2M8K2 D2M8K2.t14895 = [0, 183713592032, 474160220529, 208366686251, 7913321096, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
