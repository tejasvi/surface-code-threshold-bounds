import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9772 = true := by
  decide +kernel

theorem tot9772 : totK PD2M8K2 D2M8K2.t9772 = [0, 172608502819, 463764224750, 247369574601, 15216174155, 0, 0, 0] := by
  decide +kernel

theorem rows9773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9773 = true := by
  decide +kernel

theorem tot9773 : totK PD2M8K2 D2M8K2.t9773 = [0, 0, 272369663440, 511647945827, 115259591113, 1198073392, 0, 0] := by
  decide +kernel

theorem rows9774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9774 = true := by
  decide +kernel

theorem tot9774 : totK PD2M8K2 D2M8K2.t9774 = [0, 29320472857, 203398202011, 438034073803, 192332479614, 12052611869, 0, 0] := by
  decide +kernel

theorem rows9775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9775 = true := by
  decide +kernel

theorem tot9775 : totK PD2M8K2 D2M8K2.t9775 = [0, 194209854023, 459442788006, 216413781061, 15520090079, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
