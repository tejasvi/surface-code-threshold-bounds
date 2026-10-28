import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5788 = true := by
  decide +kernel

theorem tot5788 : totK PA10K2 A10K2.t5788 = [0, 0, 272194063322, 1166139651768, 1892397109570, 1187928690066, 184255382452, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5789 = true := by
  decide +kernel

theorem tot5789 : totK PA10K2 A10K2.t5789 = [0, 0, 279651538817, 1445442419704, 2090516008243, 832413275859, 57219825927, 0, 0, 0] := by
  decide +kernel

theorem rows5790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5790 = true := by
  decide +kernel

theorem tot5790 : totK PA10K2 A10K2.t5790 = [0, 0, 249334213227, 898712864117, 1548043932616, 1461846825750, 412757249934, 31333686660, 0, 0] := by
  decide +kernel

theorem rows5791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5791 = true := by
  decide +kernel

theorem tot5791 : totK PA10K2 A10K2.t5791 = [0, 0, 432572230118, 1626705485814, 1894788087771, 661503452712, 52232171148, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
