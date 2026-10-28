import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11552 = true := by
  decide +kernel

theorem tot11552 : totK PD2M8K2 D2M8K2.t11552 = [0, 0, 157672966600, 439969935622, 274246426788, 22763282260, 0, 0] := by
  decide +kernel

theorem rows11553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11553 = true := by
  decide +kernel

theorem tot11553 : totK PD2M8K2 D2M8K2.t11553 = [0, 0, 87579699114, 414281343587, 369889434095, 29158068543, 0, 0] := by
  decide +kernel

theorem rows11554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11554 = true := by
  decide +kernel

theorem tot11554 : totK PD2M8K2 D2M8K2.t11554 = [0, 0, 70791704501, 331693188483, 386575654844, 83064566166, 1332468113, 0] := by
  decide +kernel

theorem rows11555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11555 = true := by
  decide +kernel

theorem tot11555 : totK PD2M8K2 D2M8K2.t11555 = [0, 0, 174461140706, 459248801321, 257050311848, 19822803090, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
