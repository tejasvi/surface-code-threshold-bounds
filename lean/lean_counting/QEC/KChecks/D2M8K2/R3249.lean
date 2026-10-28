import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12996 = true := by
  decide +kernel

theorem tot12996 : totK PD2M8K2 D2M8K2.t12996 = [0, 0, 203724087529, 481891850181, 209074727248, 7994456143, 0, 0] := by
  decide +kernel

theorem rows12997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12997 = true := by
  decide +kernel

theorem tot12997 : totK PD2M8K2 D2M8K2.t12997 = [0, 84808482832, 265786586842, 366073690800, 171194757519, 6833968568, 0, 0] := by
  decide +kernel

theorem rows12998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12998 = true := by
  decide +kernel

theorem tot12998 : totK PD2M8K2 D2M8K2.t12998 = [0, 180556317488, 465951520778, 253251711488, 22908233461, 0, 0, 0] := by
  decide +kernel

theorem rows12999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12999 = true := by
  decide +kernel

theorem tot12999 : totK PD2M8K2 D2M8K2.t12999 = [0, 160348302782, 452799344412, 262372641350, 21551683941, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
