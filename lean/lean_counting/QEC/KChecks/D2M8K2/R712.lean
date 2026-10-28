import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2848 = true := by
  decide +kernel

theorem tot2848 : totK PD2M8K2 D2M8K2.t2848 = [0, 0, 308128792566, 494346768050, 100888586247, 2909416399, 0, 0] := by
  decide +kernel

theorem rows2849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2849 = true := by
  decide +kernel

theorem tot2849 : totK PD2M8K2 D2M8K2.t2849 = [0, 90132371221, 308895302902, 390312893553, 107339420434, 2250452236, 0, 0] := by
  decide +kernel

theorem rows2850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2850 = true := by
  decide +kernel

theorem tot2850 : totK PD2M8K2 D2M8K2.t2850 = [0, 171311297230, 439631486856, 281851246055, 30315466679, 0, 0, 0] := by
  decide +kernel

theorem rows2851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2851 = true := by
  decide +kernel

theorem tot2851 : totK PD2M8K2 D2M8K2.t2851 = [0, 84500633991, 417274788118, 371858178536, 41844487877, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
