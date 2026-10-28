import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7136 = true := by
  decide +kernel

theorem tot7136 : totK PD2M8K2 D2M8K2.t7136 = [0, 0, 0, 310235562819, 457682153660, 80313500305, 1239866073, 0] := by
  decide +kernel

theorem rows7137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7137 = true := by
  decide +kernel

theorem tot7137 : totK PD2M8K2 D2M8K2.t7137 = [0, 0, 211300962780, 479181229032, 205941472951, 10682572035, 0, 0] := by
  decide +kernel

theorem rows7138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7138 = true := by
  decide +kernel

theorem tot7138 : totK PD2M8K2 D2M8K2.t7138 = [0, 0, 188954591593, 466629413627, 213978776101, 12439805748, 0, 0] := by
  decide +kernel

theorem rows7139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7139 = true := by
  decide +kernel

theorem tot7139 : totK PD2M8K2 D2M8K2.t7139 = [0, 0, 176132972186, 489307352319, 216814051624, 10376406296, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
