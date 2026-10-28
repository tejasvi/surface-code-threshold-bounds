import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12816 = true := by
  decide +kernel

theorem tot12816 : totK PD2M8K2 D2M8K2.t12816 = [0, 0, 0, 255229720281, 486844607070, 133493991840, 2318623666, 0] := by
  decide +kernel

theorem rows12817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12817 = true := by
  decide +kernel

theorem tot12817 : totK PD2M8K2 D2M8K2.t12817 = [0, 0, 66967892138, 269649710553, 367275379349, 140999209215, 10786826731, 0] := by
  decide +kernel

theorem rows12818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12818 = true := by
  decide +kernel

theorem tot12818 : totK PD2M8K2 D2M8K2.t12818 = [0, 0, 163124823668, 493279730837, 236979409169, 11071105621, 0, 0] := by
  decide +kernel

theorem rows12819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12819 = true := by
  decide +kernel

theorem tot12819 : totK PD2M8K2 D2M8K2.t12819 = [0, 0, 179118419696, 470664936730, 235310869179, 14968048825, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
