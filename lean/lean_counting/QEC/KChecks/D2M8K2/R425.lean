import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1700 = true := by
  decide +kernel

theorem tot1700 : totK PD2M8K2 D2M8K2.t1700 = [0, 0, 0, 242767769544, 484198889254, 158766161446, 9473784440, 0] := by
  decide +kernel

theorem rows1701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1701 = true := by
  decide +kernel

theorem tot1701 : totK PD2M8K2 D2M8K2.t1701 = [0, 0, 0, 166612642975, 457459224916, 211814776970, 14738434662, 0] := by
  decide +kernel

theorem rows1702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1702 = true := by
  decide +kernel

theorem tot1702 : totK PD2M8K2 D2M8K2.t1702 = [0, 0, 0, 242908135969, 480248773414, 158082140088, 7414397321, 0] := by
  decide +kernel

theorem rows1703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1703 = true := by
  decide +kernel

theorem tot1703 : totK PD2M8K2 D2M8K2.t1703 = [0, 0, 0, 166671405009, 456507389804, 212915466172, 14813713234, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
