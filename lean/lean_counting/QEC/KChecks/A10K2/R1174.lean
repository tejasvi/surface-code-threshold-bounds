import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4696 = true := by
  decide +kernel

theorem tot4696 : totK PA10K2 A10K2.t4696 = [0, 0, 580505091777, 1874855838588, 1696072114740, 495148744866, 143038997426, 29150846468, 0, 0] := by
  decide +kernel

theorem rows4697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4697 = true := by
  decide +kernel

theorem tot4697 : totK PA10K2 A10K2.t4697 = [0, 0, 285900980352, 1486679653333, 2223559762115, 866049564251, 67810673029, 0, 0, 0] := by
  decide +kernel

theorem rows4698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4698 = true := by
  decide +kernel

theorem tot4698 : totK PA10K2 A10K2.t4698 = [0, 0, 0, 469065023964, 1806514776122, 1870711311117, 501760087653, 31768748853, 0, 0] := by
  decide +kernel

theorem rows4699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4699 = true := by
  decide +kernel

theorem tot4699 : totK PA10K2 A10K2.t4699 = [0, 0, 444976671088, 1663565469319, 1861441844192, 724578169577, 78737207659, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
