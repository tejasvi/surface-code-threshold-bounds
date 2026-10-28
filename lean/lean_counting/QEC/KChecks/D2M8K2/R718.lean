import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2872 = true := by
  decide +kernel

theorem tot2872 : totK PD2M8K2 D2M8K2.t2872 = [0, 204646494783, 494315554662, 180747583103, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows2873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2873 = true := by
  decide +kernel

theorem tot2873 : totK PD2M8K2 D2M8K2.t2873 = [170158465841, 442192807336, 250288071367, 35688696210, 1503593968, 0, 0, 0] := by
  decide +kernel

theorem rows2874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2874 = true := by
  decide +kernel

theorem tot2874 : totK PD2M8K2 D2M8K2.t2874 = [154487648080, 424551181726, 288823151683, 31434552815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2875 = true := by
  decide +kernel

theorem tot2875 : totK PD2M8K2 D2M8K2.t2875 = [91398613323, 362562306018, 346540484230, 66445412119, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
