import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3056 = true := by
  decide +kernel

theorem tot3056 : totK PD2M8K2 D2M8K2.t3056 = [0, 174156663994, 454979751476, 249948438223, 22726924806, 0, 0, 0] := by
  decide +kernel

theorem rows3057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3057 = true := by
  decide +kernel

theorem tot3057 : totK PD2M8K2 D2M8K2.t3057 = [0, 196927345499, 475067737331, 220832150756, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows3058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3058 = true := by
  decide +kernel

theorem tot3058 : totK PD2M8K2 D2M8K2.t3058 = [0, 18811892075, 309022633552, 463551296233, 93062062943, 1164319620, 0, 0] := by
  decide +kernel

theorem rows3059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3059 = true := by
  decide +kernel

theorem tot3059 : totK PD2M8K2 D2M8K2.t3059 = [0, 0, 200979893560, 470490719921, 190287648090, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
