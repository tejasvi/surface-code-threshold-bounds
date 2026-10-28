import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5884 = true := by
  decide +kernel

theorem tot5884 : totK PD2M8K2 D2M8K2.t5884 = [185604412992, 442645543320, 214652220349, 44081969006, 7093611788, 0, 0, 0] := by
  decide +kernel

theorem rows5885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5885 = true := by
  decide +kernel

theorem tot5885 : totK PD2M8K2 D2M8K2.t5885 = [137972160625, 445737150933, 283743100904, 23470772497, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5886 = true := by
  decide +kernel

theorem tot5886 : totK PD2M8K2 D2M8K2.t5886 = [19982170097, 279299874136, 492608685606, 107760526006, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows5887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5887 = true := by
  decide +kernel

theorem tot5887 : totK PD2M8K2 D2M8K2.t5887 = [167255114105, 436100779932, 278836020943, 30474664319, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
