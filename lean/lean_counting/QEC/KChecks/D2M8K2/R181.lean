import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t724 = true := by
  decide +kernel

theorem tot724 : totK PD2M8K2 D2M8K2.t724 = [37663951278, 316185606364, 442390924062, 99051637713, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t725 = true := by
  decide +kernel

theorem tot725 : totK PD2M8K2 D2M8K2.t725 = [72256902324, 362429996628, 423108814549, 54623246706, 0, 0, 0, 0] := by
  decide +kernel

theorem rows726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t726 = true := by
  decide +kernel

theorem tot726 : totK PD2M8K2 D2M8K2.t726 = [172667595995, 448548154663, 271626411583, 27708936516, 0, 0, 0, 0] := by
  decide +kernel

theorem rows727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t727 = true := by
  decide +kernel

theorem tot727 : totK PD2M8K2 D2M8K2.t727 = [143432784708, 454425492548, 292397103949, 23465344458, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
