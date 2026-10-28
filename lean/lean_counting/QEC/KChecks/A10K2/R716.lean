import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2864 = true := by
  decide +kernel

theorem tot2864 : totK PA10K2 A10K2.t2864 = [0, 0, 287020209470, 1417804099802, 2140488244726, 934280793747, 84917271460, 0, 0, 0] := by
  decide +kernel

theorem rows2865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2865 = true := by
  decide +kernel

theorem tot2865 : totK PA10K2 A10K2.t2865 = [0, 0, 9392774405, 527618588481, 1785279921276, 1750165337930, 476318389987, 31018567651, 0, 0] := by
  decide +kernel

theorem rows2866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2866 = true := by
  decide +kernel

theorem tot2866 : totK PA10K2 A10K2.t2866 = [0, 0, 588100508459, 1869276173753, 1773596229431, 480229334948, 31821298896, 0, 0, 0] := by
  decide +kernel

theorem rows2867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2867 = true := by
  decide +kernel

theorem tot2867 : totK PA10K2 A10K2.t2867 = [0, 0, 39815911663, 1068684440644, 2332564784433, 1085363880456, 77916801148, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
