import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1984 = true := by
  decide +kernel

theorem tot1984 : totK PD2M8K2 D2M8K2.t1984 = [0, 90363393300, 363931646146, 357840682896, 71180873986, 1096156699, 0, 0] := by
  decide +kernel

theorem rows1985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1985 = true := by
  decide +kernel

theorem tot1985 : totK PD2M8K2 D2M8K2.t1985 = [0, 0, 294813684250, 512449478025, 97628518190, 1067382613, 0, 0] := by
  decide +kernel

theorem rows1986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1986 = true := by
  decide +kernel

theorem tot1986 : totK PD2M8K2 D2M8K2.t1986 = [0, 170933425947, 416630611458, 268187231671, 56589336268, 2813333534, 0, 0] := by
  decide +kernel

theorem rows1987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1987 = true := by
  decide +kernel

theorem tot1987 : totK PD2M8K2 D2M8K2.t1987 = [0, 196906397726, 475988350337, 221822283698, 14007037492, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
