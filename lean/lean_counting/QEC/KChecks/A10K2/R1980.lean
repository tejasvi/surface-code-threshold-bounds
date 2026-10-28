import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7920 = true := by
  decide +kernel

theorem tot7920 : totK PA10K2 A10K2.t7920 = [0, 0, 589953312777, 1913709911820, 1887462292279, 603041812138, 49164041343, 0, 0, 0] := by
  decide +kernel

theorem rows7921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7921 = true := by
  decide +kernel

theorem tot7921 : totK PA10K2 A10K2.t7921 = [0, 0, 472079418039, 1795763432421, 1917029095473, 524549487958, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows7922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7922 = true := by
  decide +kernel

theorem tot7922 : totK PA10K2 A10K2.t7922 = [0, 0, 60690433792, 849379737977, 2065153281551, 1499994314067, 346757965687, 18713227901, 0, 0] := by
  decide +kernel

theorem rows7923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7923 = true := by
  decide +kernel

theorem tot7923 : totK PA10K2 A10K2.t7923 = [0, 0, 272315391523, 1242448713338, 1885457588761, 1157444130557, 163931400087, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
