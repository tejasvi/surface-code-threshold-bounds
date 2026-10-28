import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2796 = true := by
  decide +kernel

theorem tot2796 : totK PA10K2 A10K2.t2796 = [0, 576941670327, 1972486416404, 1983516184978, 558982900430, 32570803390, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2797 = true := by
  decide +kernel

theorem tot2797 : totK PA10K2 A10K2.t2797 = [0, 0, 806536064198, 2254412961805, 1656368381680, 285227831001, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows2798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2798 = true := by
  decide +kernel

theorem tot2798 : totK PA10K2 A10K2.t2798 = [0, 0, 670472857671, 2055107123556, 1786471400138, 450939366280, 28177825909, 0, 0, 0] := by
  decide +kernel

theorem rows2799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2799 = true := by
  decide +kernel

theorem tot2799 : totK PA10K2 A10K2.t2799 = [0, 0, 472735052216, 1790959491650, 1917750406257, 508386052174, 31222411477, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
