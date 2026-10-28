import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t240 = true := by
  decide +kernel

theorem tot240 : totK PD2M8K2 D2M8K2.t240 = [0, 45612846879, 285275628010, 447308512178, 109231159945, 3821179711, 0, 0] := by
  decide +kernel

theorem rows241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t241 = true := by
  decide +kernel

theorem tot241 : totK PD2M8K2 D2M8K2.t241 = [0, 183771300262, 465700079204, 236583679762, 20989658024, 0, 0, 0] := by
  decide +kernel

theorem rows242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t242 = true := by
  decide +kernel

theorem tot242 : totK PD2M8K2 D2M8K2.t242 = [0, 180982683096, 470717769808, 249408355088, 13842663846, 0, 0, 0] := by
  decide +kernel

theorem rows243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t243 = true := by
  decide +kernel

theorem tot243 : totK PD2M8K2 D2M8K2.t243 = [0, 0, 273980588132, 500494363001, 110123768632, 1232609433, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
