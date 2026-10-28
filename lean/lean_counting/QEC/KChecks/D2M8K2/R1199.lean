import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4796 = true := by
  decide +kernel

theorem tot4796 : totK PD2M8K2 D2M8K2.t4796 = [0, 89109335774, 353130666884, 393099859674, 78041571860, 1164319620, 0, 0] := by
  decide +kernel

theorem rows4797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4797 = true := by
  decide +kernel

theorem tot4797 : totK PD2M8K2 D2M8K2.t4797 = [0, 57143226307, 285318765575, 416945592480, 134581178558, 7018013031, 0, 0] := by
  decide +kernel

theorem rows4798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4798 = true := by
  decide +kernel

theorem tot4798 : totK PD2M8K2 D2M8K2.t4798 = [0, 184150174085, 459087306237, 250438122024, 23073763248, 0, 0, 0] := by
  decide +kernel

theorem rows4799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4799 = true := by
  decide +kernel

theorem tot4799 : totK PD2M8K2 D2M8K2.t4799 = [0, 179659960599, 475598012100, 234141544538, 13758549984, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
