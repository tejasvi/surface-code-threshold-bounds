import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7472 = true := by
  decide +kernel

theorem tot7472 : totK PD2M8K2 D2M8K2.t7472 = [0, 0, 174592541994, 449116376508, 265623406469, 24998281750, 0, 0] := by
  decide +kernel

theorem rows7473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7473 = true := by
  decide +kernel

theorem tot7473 : totK PD2M8K2 D2M8K2.t7473 = [0, 0, 148372485598, 456780089659, 286778943554, 20233399704, 0, 0] := by
  decide +kernel

theorem rows7474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7474 = true := by
  decide +kernel

theorem tot7474 : totK PD2M8K2 D2M8K2.t7474 = [0, 0, 0, 221105979428, 484439590509, 153921720953, 4811815119, 0] := by
  decide +kernel

theorem rows7475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7475 = true := by
  decide +kernel

theorem tot7475 : totK PD2M8K2 D2M8K2.t7475 = [0, 37283609705, 39621360432, 175977725361, 424737664457, 190492163314, 13202337522, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
