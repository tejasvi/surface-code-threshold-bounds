import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2500 = true := by
  decide +kernel

theorem tot2500 : totK PD2M8K2 D2M8K2.t2500 = [0, 0, 303105525185, 466346897700, 85960386986, 1206465782, 0, 0] := by
  decide +kernel

theorem rows2501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2501 = true := by
  decide +kernel

theorem tot2501 : totK PD2M8K2 D2M8K2.t2501 = [0, 149430685018, 424066527454, 317777966645, 34862993753, 0, 0, 0] := by
  decide +kernel

theorem rows2502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2502 = true := by
  decide +kernel

theorem tot2502 : totK PD2M8K2 D2M8K2.t2502 = [0, 192271821599, 487741548089, 219107848006, 11405872210, 0, 0, 0] := by
  decide +kernel

theorem rows2503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2503 = true := by
  decide +kernel

theorem tot2503 : totK PD2M8K2 D2M8K2.t2503 = [0, 169360159580, 458920145023, 242388403116, 15606283322, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
