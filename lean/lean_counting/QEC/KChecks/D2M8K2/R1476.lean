import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5904 = true := by
  decide +kernel

theorem tot5904 : totK PD2M8K2 D2M8K2.t5904 = [0, 183894632943, 454182885565, 222976069288, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows5905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5905 = true := by
  decide +kernel

theorem tot5905 : totK PD2M8K2 D2M8K2.t5905 = [0, 53791256002, 352624613070, 383576777233, 66301157475, 1138244013, 0, 0] := by
  decide +kernel

theorem rows5906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5906 = true := by
  decide +kernel

theorem tot5906 : totK PD2M8K2 D2M8K2.t5906 = [0, 100548816168, 386150337958, 373221846228, 45881590847, 0, 0, 0] := by
  decide +kernel

theorem rows5907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5907 = true := by
  decide +kernel

theorem tot5907 : totK PD2M8K2 D2M8K2.t5907 = [0, 199090069696, 473273937964, 207929896458, 14633607569, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
