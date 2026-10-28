import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12100 = true := by
  decide +kernel

theorem tot12100 : totK PD2M8K2 D2M8K2.t12100 = [0, 32937304211, 280999632724, 459589309188, 111518196808, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12101 = true := by
  decide +kernel

theorem tot12101 : totK PD2M8K2 D2M8K2.t12101 = [0, 181556596654, 447271689201, 246494746295, 22616335593, 0, 0, 0] := by
  decide +kernel

theorem rows12102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12102 = true := by
  decide +kernel

theorem tot12102 : totK PD2M8K2 D2M8K2.t12102 = [0, 185228615791, 486528163687, 232988447202, 10954547177, 0, 0, 0] := by
  decide +kernel

theorem rows12103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12103 = true := by
  decide +kernel

theorem tot12103 : totK PD2M8K2 D2M8K2.t12103 = [0, 0, 271257425933, 484184111700, 112266453198, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
