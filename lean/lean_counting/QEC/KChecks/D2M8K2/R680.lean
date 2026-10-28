import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2720 = true := by
  decide +kernel

theorem tot2720 : totK PD2M8K2 D2M8K2.t2720 = [0, 0, 86235217742, 419072210458, 349145778132, 30832330659, 0, 0] := by
  decide +kernel

theorem rows2721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2721 = true := by
  decide +kernel

theorem tot2721 : totK PD2M8K2 D2M8K2.t2721 = [0, 0, 0, 220081946743, 478172727317, 155202154934, 5352782441, 0] := by
  decide +kernel

theorem rows2722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2722 = true := by
  decide +kernel

theorem tot2722 : totK PD2M8K2 D2M8K2.t2722 = [0, 0, 162431043770, 449975341607, 256835641802, 23697586691, 0, 0] := by
  decide +kernel

theorem rows2723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2723 = true := by
  decide +kernel

theorem tot2723 : totK PD2M8K2 D2M8K2.t2723 = [0, 0, 190380459403, 473453040742, 222750573201, 11199163505, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
