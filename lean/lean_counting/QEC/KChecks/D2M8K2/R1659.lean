import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6636 = true := by
  decide +kernel

theorem tot6636 : totK PD2M8K2 D2M8K2.t6636 = [0, 0, 193901155646, 448813173532, 201529528952, 16650337807, 0, 0] := by
  decide +kernel

theorem rows6637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6637 = true := by
  decide +kernel

theorem tot6637 : totK PD2M8K2 D2M8K2.t6637 = [0, 0, 214064530601, 492053246119, 172951759388, 5265834820, 0, 0] := by
  decide +kernel

theorem rows6638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6638 = true := by
  decide +kernel

theorem tot6638 : totK PD2M8K2 D2M8K2.t6638 = [0, 111980144520, 396916401609, 371067613419, 54268313268, 0, 0, 0] := by
  decide +kernel

theorem rows6639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6639 = true := by
  decide +kernel

theorem tot6639 : totK PD2M8K2 D2M8K2.t6639 = [0, 189824758684, 464573958611, 238108306554, 14591369033, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
