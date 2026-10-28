import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1740 = true := by
  decide +kernel

theorem tot1740 : totK PA10K2 A10K2.t1740 = [0, 0, 0, 495351043662, 1879009099121, 2008551319540, 596986241850, 40748810791, 0, 0] := by
  decide +kernel

theorem rows1741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1741 = true := by
  decide +kernel

theorem tot1741 : totK PA10K2 A10K2.t1741 = [0, 0, 0, 26497999062, 795997004280, 2244430653906, 1523262362126, 260307558448, 6904928264, 0] := by
  decide +kernel

theorem rows1742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1742 = true := by
  decide +kernel

theorem tot1742 : totK PA10K2 A10K2.t1742 = [0, 0, 0, 754143282575, 2305431986626, 1800090390663, 311730717126, 11695391137, 0, 0] := by
  decide +kernel

theorem rows1743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1743 = true := by
  decide +kernel

theorem tot1743 : totK PA10K2 A10K2.t1743 = [0, 0, 414502387968, 1368056062089, 1676523950298, 1101697538090, 358676652854, 30622793463, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
