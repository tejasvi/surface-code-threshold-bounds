import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6000 = true := by
  decide +kernel

theorem tot6000 : totK PA10K2 A10K2.t6000 = [0, 465036241678, 1776982461918, 1948307295462, 552700889767, 31987876949, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6001 = true := by
  decide +kernel

theorem tot6001 : totK PA10K2 A10K2.t6001 = [0, 521480947326, 1806749601999, 1954163406589, 596424397918, 32911643181, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6002 = true := by
  decide +kernel

theorem tot6002 : totK PA10K2 A10K2.t6002 = [0, 477595728650, 1797831968929, 1902052207903, 487962620477, 31088438951, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6003 = true := by
  decide +kernel

theorem tot6003 : totK PA10K2 A10K2.t6003 = [0, 377887365021, 1725617780457, 1991623771119, 541434830235, 31889781550, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
