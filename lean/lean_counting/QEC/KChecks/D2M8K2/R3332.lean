import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13328 = true := by
  decide +kernel

theorem tot13328 : totK PD2M8K2 D2M8K2.t13328 = [0, 175298174919, 399062705612, 238001783604, 90990535731, 5415877171, 0, 0] := by
  decide +kernel

theorem rows13329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13329 = true := by
  decide +kernel

theorem tot13329 : totK PD2M8K2 D2M8K2.t13329 = [0, 181087757825, 444453822365, 268937168827, 26681650413, 0, 0, 0] := by
  decide +kernel

theorem rows13330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13330 = true := by
  decide +kernel

theorem tot13330 : totK PD2M8K2 D2M8K2.t13330 = [0, 83518256830, 381709458936, 360661721596, 55739712849, 1198073392, 0, 0] := by
  decide +kernel

theorem rows13331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13331 = true := by
  decide +kernel

theorem tot13331 : totK PD2M8K2 D2M8K2.t13331 = [0, 0, 230471162643, 496162387164, 168611226989, 8470662040, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
