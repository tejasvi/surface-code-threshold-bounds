import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2804 = true := by
  decide +kernel

theorem tot2804 : totK PA10K2 A10K2.t2804 = [0, 115548944004, 767958234631, 1851694908700, 1803638288403, 533685315836, 43911449185, 0, 0, 0] := by
  decide +kernel

theorem rows2805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2805 = true := by
  decide +kernel

theorem tot2805 : totK PA10K2 A10K2.t2805 = [0, 550057923901, 1901424974592, 1883840715987, 508293019413, 31301336365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2806 = true := by
  decide +kernel

theorem tot2806 : totK PA10K2 A10K2.t2806 = [0, 118334424620, 1002315523562, 2121418994459, 1382927310146, 275823195822, 20058242317, 0, 0, 0] := by
  decide +kernel

theorem rows2807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2807 = true := by
  decide +kernel

theorem tot2807 : totK PA10K2 A10K2.t2807 = [0, 287262473290, 1359379234374, 2047655533466, 1093826281901, 185263669189, 5255105852, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
