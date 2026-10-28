import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6968 = true := by
  decide +kernel

theorem tot6968 : totK PD2M8K2 D2M8K2.t6968 = [0, 164699952579, 456238010246, 266157262528, 20781770327, 0, 0, 0] := by
  decide +kernel

theorem rows6969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6969 = true := by
  decide +kernel

theorem tot6969 : totK PD2M8K2 D2M8K2.t6969 = [0, 0, 261412754287, 502300063825, 129726504491, 1268739303, 0, 0] := by
  decide +kernel

theorem rows6970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6970 = true := by
  decide +kernel

theorem tot6970 : totK PD2M8K2 D2M8K2.t6970 = [0, 0, 163669658975, 462619677767, 232910242073, 12134001689, 0, 0] := by
  decide +kernel

theorem rows6971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6971 = true := by
  decide +kernel

theorem tot6971 : totK PD2M8K2 D2M8K2.t6971 = [0, 0, 187097362634, 471216984867, 213068461382, 13996260341, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
