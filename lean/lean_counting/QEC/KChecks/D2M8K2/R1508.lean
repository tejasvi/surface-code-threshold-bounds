import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6032 = true := by
  decide +kernel

theorem tot6032 : totK PD2M8K2 D2M8K2.t6032 = [0, 0, 207355501231, 494859819279, 196202949729, 5430665091, 0, 0] := by
  decide +kernel

theorem rows6033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6033 = true := by
  decide +kernel

theorem tot6033 : totK PD2M8K2 D2M8K2.t6033 = [0, 161387171172, 365746263967, 262594880141, 105548996118, 6756203132, 0, 0] := by
  decide +kernel

theorem rows6034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6034 = true := by
  decide +kernel

theorem tot6034 : totK PD2M8K2 D2M8K2.t6034 = [0, 159431063195, 439090118196, 288859646497, 30437197709, 0, 0, 0] := by
  decide +kernel

theorem rows6035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6035 = true := by
  decide +kernel

theorem tot6035 : totK PD2M8K2 D2M8K2.t6035 = [0, 106049517710, 408880993609, 335317452396, 39754928795, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
