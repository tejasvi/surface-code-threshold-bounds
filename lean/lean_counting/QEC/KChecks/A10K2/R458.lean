import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1832 = true := by
  decide +kernel

theorem tot1832 : totK PA10K2 A10K2.t1832 = [0, 0, 318259614394, 1525709376915, 2129568572374, 837880950661, 74778429178, 0, 0, 0] := by
  decide +kernel

theorem rows1833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1833 = true := by
  decide +kernel

theorem tot1833 : totK PA10K2 A10K2.t1833 = [0, 0, 539359403661, 1936803813435, 1947560466089, 444863228873, 12350643961, 0, 0, 0] := by
  decide +kernel

theorem rows1834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1834 = true := by
  decide +kernel

theorem tot1834 : totK PA10K2 A10K2.t1834 = [0, 0, 0, 617440558575, 1999553489731, 1604776709790, 384164769889, 25239774317, 0, 0] := by
  decide +kernel

theorem rows1835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1835 = true := by
  decide +kernel

theorem tot1835 : totK PA10K2 A10K2.t1835 = [0, 0, 290974432811, 1304572923414, 1901272413382, 1084754501015, 184553432580, 5410721913, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
