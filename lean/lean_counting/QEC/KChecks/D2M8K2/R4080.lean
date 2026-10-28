import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16320 = true := by
  decide +kernel

theorem tot16320 : totK PD2M8K2 D2M8K2.t16320 = [0, 0, 221208825897, 508788471905, 185866686017, 6685346624, 0, 0] := by
  decide +kernel

theorem rows16321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16321 = true := by
  decide +kernel

theorem tot16321 : totK PD2M8K2 D2M8K2.t16321 = [0, 0, 0, 280836941769, 478481004623, 151983434442, 10519103133, 0] := by
  decide +kernel

theorem rows16322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16322 = true := by
  decide +kernel

theorem tot16322 : totK PD2M8K2 D2M8K2.t16322 = [0, 0, 18548618087, 239842271281, 470707081395, 176880982719, 5774780012, 0] := by
  decide +kernel

theorem rows16323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16323 = true := by
  decide +kernel

theorem tot16323 : totK PD2M8K2 D2M8K2.t16323 = [0, 0, 189202578032, 457762951033, 242698236176, 22506143075, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
