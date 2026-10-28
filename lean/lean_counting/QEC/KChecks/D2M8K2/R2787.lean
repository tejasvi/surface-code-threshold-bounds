import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11148 = true := by
  decide +kernel

theorem tot11148 : totK PD2M8K2 D2M8K2.t11148 = [0, 177395290926, 471594390567, 254394780706, 20205781078, 0, 0, 0] := by
  decide +kernel

theorem rows11149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11149 = true := by
  decide +kernel

theorem tot11149 : totK PD2M8K2 D2M8K2.t11149 = [0, 172604570348, 462215375818, 245674805709, 15117888121, 0, 0, 0] := by
  decide +kernel

theorem rows11150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11150 = true := by
  decide +kernel

theorem tot11150 : totK PD2M8K2 D2M8K2.t11150 = [0, 0, 285092638136, 509118913765, 104800701371, 1164319620, 0, 0] := by
  decide +kernel

theorem rows11151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11151 = true := by
  decide +kernel

theorem tot11151 : totK PD2M8K2 D2M8K2.t11151 = [0, 22021801666, 202251433844, 449306123528, 184963979403, 11885407614, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
