import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14964 = true := by
  decide +kernel

theorem tot14964 : totK PD2M8K2 D2M8K2.t14964 = [0, 152814491134, 440194260209, 253416639465, 16423975347, 0, 0, 0] := by
  decide +kernel

theorem rows14965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14965 = true := by
  decide +kernel

theorem tot14965 : totK PD2M8K2 D2M8K2.t14965 = [0, 73054734499, 339565234301, 392144004235, 85263485121, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14966 = true := by
  decide +kernel

theorem tot14966 : totK PD2M8K2 D2M8K2.t14966 = [0, 40738718386, 343167214807, 459667127463, 55980462615, 0, 0, 0] := by
  decide +kernel

theorem rows14967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14967 = true := by
  decide +kernel

theorem tot14967 : totK PD2M8K2 D2M8K2.t14967 = [0, 167417013632, 444467963591, 282258427461, 30455970377, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
