import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1732 = true := by
  decide +kernel

theorem tot1732 : totK PD2M8K2 D2M8K2.t1732 = [0, 0, 173823516313, 461193525859, 247762350199, 15041965618, 0, 0] := by
  decide +kernel

theorem rows1733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1733 = true := by
  decide +kernel

theorem tot1733 : totK PD2M8K2 D2M8K2.t1733 = [0, 0, 0, 279339430696, 495735015057, 118172041286, 2329117419, 0] := by
  decide +kernel

theorem rows1734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1734 = true := by
  decide +kernel

theorem tot1734 : totK PD2M8K2 D2M8K2.t1734 = [0, 0, 52052575639, 243594853644, 404080838045, 145512902303, 10841558499, 0] := by
  decide +kernel

theorem rows1735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1735 = true := by
  decide +kernel

theorem tot1735 : totK PD2M8K2 D2M8K2.t1735 = [0, 0, 176415537549, 469317333196, 224018734860, 6827368633, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
