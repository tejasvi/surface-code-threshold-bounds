import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4044 = true := by
  decide +kernel

theorem tot4044 : totK PA10K2 A10K2.t4044 = [0, 0, 286550501063, 1505205795408, 2182994884946, 818831636876, 66477122807, 0, 0, 0] := by
  decide +kernel

theorem rows4045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4045 = true := by
  decide +kernel

theorem tot4045 : totK PA10K2 A10K2.t4045 = [0, 0, 539466270671, 1978798449676, 2109202856250, 575246763663, 18888950833, 0, 0, 0] := by
  decide +kernel

theorem rows4046 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4046 = true := by
  decide +kernel

theorem tot4046 : totK PA10K2 A10K2.t4046 = [0, 0, 0, 624420167701, 2157808564645, 1924781778100, 334557998021, 6853348008, 0, 0] := by
  decide +kernel

theorem rows4047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4047 = true := by
  decide +kernel

theorem tot4047 : totK PA10K2 A10K2.t4047 = [0, 0, 0, 516048606538, 1781872255050, 1942233570941, 690356520304, 55498468803, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
