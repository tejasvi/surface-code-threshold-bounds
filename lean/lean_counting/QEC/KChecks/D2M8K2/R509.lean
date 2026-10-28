import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2036 = true := by
  decide +kernel

theorem tot2036 : totK PD2M8K2 D2M8K2.t2036 = [0, 0, 84636411730, 336245167349, 347120737447, 84771506168, 3667207281, 0] := by
  decide +kernel

theorem rows2037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2037 = true := by
  decide +kernel

theorem tot2037 : totK PD2M8K2 D2M8K2.t2037 = [0, 0, 189308830849, 454615052794, 237096388553, 15551741900, 0, 0] := by
  decide +kernel

theorem rows2038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2038 = true := by
  decide +kernel

theorem tot2038 : totK PD2M8K2 D2M8K2.t2038 = [0, 36508988125, 193921132050, 414292517978, 249261956185, 20249401196, 0, 0] := by
  decide +kernel

theorem rows2039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2039 = true := by
  decide +kernel

theorem tot2039 : totK PD2M8K2 D2M8K2.t2039 = [0, 200995854096, 477831684324, 198782337891, 9852138406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
