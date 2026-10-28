import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2008 = true := by
  decide +kernel

theorem tot2008 : totK PD2M8K2 D2M8K2.t2008 = [0, 0, 196555484231, 449058137652, 232962906420, 20271593868, 0, 0] := by
  decide +kernel

theorem rows2009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2009 = true := by
  decide +kernel

theorem tot2009 : totK PD2M8K2 D2M8K2.t2009 = [0, 0, 200369970524, 488904541872, 196004837461, 5430665091, 0, 0] := by
  decide +kernel

theorem rows2010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2010 = true := by
  decide +kernel

theorem tot2010 : totK PD2M8K2 D2M8K2.t2010 = [0, 175934079045, 386179587603, 244628418913, 97904455068, 5372734930, 0, 0] := by
  decide +kernel

theorem rows2011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2011 = true := by
  decide +kernel

theorem tot2011 : totK PD2M8K2 D2M8K2.t2011 = [0, 162262832582, 442985179285, 288349191344, 29793303894, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
