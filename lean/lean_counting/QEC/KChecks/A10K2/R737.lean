import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2948 = true := by
  decide +kernel

theorem tot2948 : totK PA10K2 A10K2.t2948 = [0, 613762948205, 2033441011553, 1892579267547, 479265622996, 25761627668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2949 = true := by
  decide +kernel

theorem tot2949 : totK PA10K2 A10K2.t2949 = [0, 0, 760699974023, 2275726453684, 1763570836930, 285315388139, 6279851884, 0, 0, 0] := by
  decide +kernel

theorem rows2950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2950 = true := by
  decide +kernel

theorem tot2950 : totK PA10K2 A10K2.t2950 = [0, 0, 437187003657, 1727442038577, 2111434331246, 752786687118, 56084282801, 0, 0, 0] := by
  decide +kernel

theorem rows2951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2951 = true := by
  decide +kernel

theorem tot2951 : totK PA10K2 A10K2.t2951 = [0, 0, 477332768892, 1812715319326, 1898429883095, 524887353107, 31741948405, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
