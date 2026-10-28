import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2200 = true := by
  decide +kernel

theorem tot2200 : totK PA10K2 A10K2.t2200 = [380633387599, 1675732479386, 2162421069302, 790314202791, 57721911081, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2201 = true := by
  decide +kernel

theorem tot2201 : totK PA10K2 A10K2.t2201 = [0, 549475442354, 1918656425859, 1847578792030, 488415550968, 31677228370, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2202 = true := by
  decide +kernel

theorem tot2202 : totK PA10K2 A10K2.t2202 = [542937375368, 1788423135019, 1803445442704, 678377090384, 75193993217, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2203 = true := by
  decide +kernel

theorem tot2203 : totK PA10K2 A10K2.t2203 = [330865856800, 1557901073041, 2186967754913, 901887412132, 76142392446, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
