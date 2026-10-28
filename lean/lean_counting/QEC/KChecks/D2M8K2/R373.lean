import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1492 = true := by
  decide +kernel

theorem tot1492 : totK PD2M8K2 D2M8K2.t1492 = [0, 0, 194664741572, 486604347328, 208394507326, 11453348948, 0, 0] := by
  decide +kernel

theorem rows1493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1493 = true := by
  decide +kernel

theorem tot1493 : totK PD2M8K2 D2M8K2.t1493 = [0, 0, 153567048432, 456686934021, 251002335195, 13904256362, 0, 0] := by
  decide +kernel

theorem rows1494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1494 = true := by
  decide +kernel

theorem tot1494 : totK PD2M8K2 D2M8K2.t1494 = [0, 0, 0, 248870220763, 474065666020, 114492761647, 2083783650, 0] := by
  decide +kernel

theorem rows1495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1495 = true := by
  decide +kernel

theorem tot1495 : totK PD2M8K2 D2M8K2.t1495 = [0, 0, 117086725142, 403046686477, 295749039001, 44421469375, 2703270515, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
