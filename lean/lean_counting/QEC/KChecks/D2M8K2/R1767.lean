import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7068 = true := by
  decide +kernel

theorem tot7068 : totK PD2M8K2 D2M8K2.t7068 = [0, 0, 210898602584, 489164619810, 176337593347, 4967996017, 0, 0] := by
  decide +kernel

theorem rows7069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7069 = true := by
  decide +kernel

theorem tot7069 : totK PD2M8K2 D2M8K2.t7069 = [0, 0, 184495915642, 456227522391, 214890332290, 17080783126, 0, 0] := by
  decide +kernel

theorem rows7070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7070 = true := by
  decide +kernel

theorem tot7070 : totK PD2M8K2 D2M8K2.t7070 = [0, 0, 199219185238, 480658989470, 197849489720, 9610913563, 0, 0] := by
  decide +kernel

theorem rows7071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7071 = true := by
  decide +kernel

theorem tot7071 : totK PD2M8K2 D2M8K2.t7071 = [0, 0, 192061364269, 469435744511, 203008229673, 12206147664, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
