import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7180 = true := by
  decide +kernel

theorem tot7180 : totK PD2M8K2 D2M8K2.t7180 = [0, 188021247795, 462400103507, 257605521827, 17569839127, 0, 0, 0] := by
  decide +kernel

theorem rows7181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7181 = true := by
  decide +kernel

theorem tot7181 : totK PD2M8K2 D2M8K2.t7181 = [0, 55373378173, 298655853552, 371165057995, 169419951281, 19836217340, 0, 0] := by
  decide +kernel

theorem rows7182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7182 = true := by
  decide +kernel

theorem tot7182 : totK PD2M8K2 D2M8K2.t7182 = [0, 0, 228759550561, 504540328317, 177161098687, 4386262913, 0, 0] := by
  decide +kernel

theorem rows7183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7183 = true := by
  decide +kernel

theorem tot7183 : totK PD2M8K2 D2M8K2.t7183 = [0, 166218900790, 381280294813, 247001374575, 103825029192, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
