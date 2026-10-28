import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6780 = true := by
  decide +kernel

theorem tot6780 : totK PD2M8K2 D2M8K2.t6780 = [0, 52622787700, 283394858476, 382324351636, 174539432771, 21385604922, 0, 0] := by
  decide +kernel

theorem rows6781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6781 = true := by
  decide +kernel

theorem tot6781 : totK PD2M8K2 D2M8K2.t6781 = [0, 0, 201668170383, 479866752236, 195129781711, 7658844075, 0, 0] := by
  decide +kernel

theorem rows6782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6782 = true := by
  decide +kernel

theorem tot6782 : totK PD2M8K2 D2M8K2.t6782 = [0, 67657031154, 244988445801, 389725936257, 169362283553, 7877424857, 0, 0] := by
  decide +kernel

theorem rows6783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6783 = true := by
  decide +kernel

theorem tot6783 : totK PD2M8K2 D2M8K2.t6783 = [0, 181574117857, 464661155113, 256802893271, 23032659230, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
