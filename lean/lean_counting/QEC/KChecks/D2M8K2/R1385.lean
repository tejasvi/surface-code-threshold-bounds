import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5540 = true := by
  decide +kernel

theorem tot5540 : totK PD2M8K2 D2M8K2.t5540 = [86674881168, 344404892467, 378837911156, 83847469779, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows5541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5541 = true := by
  decide +kernel

theorem tot5541 : totK PD2M8K2 D2M8K2.t5541 = [0, 327523757346, 514928722980, 65139050037, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5542 = true := by
  decide +kernel

theorem tot5542 : totK PD2M8K2 D2M8K2.t5542 = [179567697281, 444437686243, 278447141650, 33174607869, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5543 = true := by
  decide +kernel

theorem tot5543 : totK PD2M8K2 D2M8K2.t5543 = [167777921454, 469732352486, 259170408256, 18573792495, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
