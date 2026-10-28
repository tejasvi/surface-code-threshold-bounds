import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12028 = true := by
  decide +kernel

theorem tot12028 : totK PD2M8K2 D2M8K2.t12028 = [0, 160189047771, 463610388751, 259226575908, 15922837508, 0, 0, 0] := by
  decide +kernel

theorem rows12029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12029 = true := by
  decide +kernel

theorem tot12029 : totK PD2M8K2 D2M8K2.t12029 = [0, 0, 272634902899, 492773072923, 102497553633, 2160984415, 0, 0] := by
  decide +kernel

theorem rows12030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12030 = true := by
  decide +kernel

theorem tot12030 : totK PD2M8K2 D2M8K2.t12030 = [0, 88733900997, 366969301511, 336110285731, 75767548736, 2770420231, 0, 0] := by
  decide +kernel

theorem rows12031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12031 = true := by
  decide +kernel

theorem tot12031 : totK PD2M8K2 D2M8K2.t12031 = [0, 188587102452, 445225962367, 254437890267, 23977641356, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
