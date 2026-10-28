import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14008 = true := by
  decide +kernel

theorem tot14008 : totK PD2M8K2 D2M8K2.t14008 = [0, 60001520246, 293131012916, 419811531116, 118532355922, 3884009855, 0, 0] := by
  decide +kernel

theorem rows14009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14009 = true := by
  decide +kernel

theorem tot14009 : totK PD2M8K2 D2M8K2.t14009 = [0, 192483252019, 461803630848, 247429325485, 23132058183, 0, 0, 0] := by
  decide +kernel

theorem rows14010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14010 = true := by
  decide +kernel

theorem tot14010 : totK PD2M8K2 D2M8K2.t14010 = [0, 166099755219, 477747075890, 253794972664, 15256557117, 0, 0, 0] := by
  decide +kernel

theorem rows14011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14011 = true := by
  decide +kernel

theorem tot14011 : totK PD2M8K2 D2M8K2.t14011 = [0, 0, 276088750137, 496020136357, 119280573454, 1232398321, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
