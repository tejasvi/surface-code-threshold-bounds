import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6704 = true := by
  decide +kernel

theorem tot6704 : totK PA10K2 A10K2.t6704 = [0, 115548944004, 234228036019, 837282874598, 1992329085602, 1204574240000, 186031524292, 5676195732, 0, 0] := by
  decide +kernel

theorem rows6705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6705 = true := by
  decide +kernel

theorem tot6705 : totK PA10K2 A10K2.t6705 = [0, 516691890112, 1828858552906, 1913889624077, 517565253145, 31301336365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6706 = true := by
  decide +kernel

theorem tot6706 : totK PA10K2 A10K2.t6706 = [0, 160863886679, 1113152875265, 2107087245221, 1309073360525, 260324407547, 20058242317, 0, 0, 0] := by
  decide +kernel

theorem rows6707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6707 = true := by
  decide +kernel

theorem tot6707 : totK PA10K2 A10K2.t6707 = [0, 283557321311, 1288295928564, 1983066723204, 1173157835370, 202368928722, 5255105852, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
