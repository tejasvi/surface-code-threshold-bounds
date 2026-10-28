import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7816 = true := by
  decide +kernel

theorem tot7816 : totK PA10K2 A10K2.t7816 = [0, 0, 219708306998, 1176783520968, 2094631464844, 1199021650365, 236114023519, 20070762815, 0, 0] := by
  decide +kernel

theorem rows7817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7817 = true := by
  decide +kernel

theorem tot7817 : totK PA10K2 A10K2.t7817 = [0, 0, 183352022349, 841374827487, 1823781915129, 1522659302344, 334419002176, 10760911071, 0, 0] := by
  decide +kernel

theorem rows7818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7818 = true := by
  decide +kernel

theorem tot7818 : totK PA10K2 A10K2.t7818 = [0, 0, 375344432939, 1736948315591, 2101787014348, 555368971756, 32066831123, 0, 0, 0] := by
  decide +kernel

theorem rows7819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7819 = true := by
  decide +kernel

theorem tot7819 : totK PA10K2 A10K2.t7819 = [0, 0, 0, 750740583333, 2228600220476, 1496091255254, 217842839856, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
