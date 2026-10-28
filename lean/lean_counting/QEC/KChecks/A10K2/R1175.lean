import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4700 = true := by
  decide +kernel

theorem tot4700 : totK PA10K2 A10K2.t4700 = [0, 0, 278756356567, 1452898085445, 2072218255590, 723602509706, 44995361554, 0, 0, 0] := by
  decide +kernel

theorem rows4701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4701 = true := by
  decide +kernel

theorem tot4701 : totK PA10K2 A10K2.t4701 = [0, 0, 255642388011, 1130114351082, 1964855370623, 1145692737741, 181589179945, 6239673734, 0, 0] := by
  decide +kernel

theorem rows4702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4702 = true := by
  decide +kernel

theorem tot4702 : totK PA10K2 A10K2.t4702 = [0, 0, 486262743125, 1819557452767, 1972254749319, 621332501936, 33001472292, 0, 0, 0] := by
  decide +kernel

theorem rows4703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4703 = true := by
  decide +kernel

theorem tot4703 : totK PA10K2 A10K2.t4703 = [0, 0, 0, 738553743507, 2250955950985, 1716958889426, 303615896789, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
