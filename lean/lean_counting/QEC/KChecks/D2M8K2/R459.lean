import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1836 = true := by
  decide +kernel

theorem tot1836 : totK PD2M8K2 D2M8K2.t1836 = [0, 0, 179833456921, 485159187013, 235642159007, 10865654659, 0, 0] := by
  decide +kernel

theorem rows1837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1837 = true := by
  decide +kernel

theorem tot1837 : totK PD2M8K2 D2M8K2.t1837 = [0, 179396403326, 420802929628, 213762576642, 82695286940, 12299580195, 0, 0] := by
  decide +kernel

theorem rows1838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1838 = true := by
  decide +kernel

theorem tot1838 : totK PD2M8K2 D2M8K2.t1838 = [0, 173753849338, 451632627395, 231735862715, 18642817961, 0, 0, 0] := by
  decide +kernel

theorem rows1839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1839 = true := by
  decide +kernel

theorem tot1839 : totK PD2M8K2 D2M8K2.t1839 = [0, 60742459202, 326592636699, 413021317056, 92678479666, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
