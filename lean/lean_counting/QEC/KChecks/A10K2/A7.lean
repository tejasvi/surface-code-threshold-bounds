import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A6

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u415 = true := by
  rw [show A10K2.u415 = KTree.node A10K2.u413 (nat_lit 8540544) (nat_lit 15037888632) (nat_lit 0) A10K2.u414 from rfl, allE_node, arows413, irow415, arows414]
  all_goals rfl

theorem atot415 : totK PA10K2 A10K2.u415 = [809888342482, 4329933126620, 7718643108600, 4967891693093, 918563048569, 38021971230, 0, 0, 0, 0] := by
  rw [show A10K2.u415 = KTree.node A10K2.u413 (nat_lit 8540544) (nat_lit 15037888632) (nat_lit 0) A10K2.u414 from rfl, totK_node, atot413, atot414]
  decide +kernel

theorem arows418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u418 = true := by
  rw [show A10K2.u418 = KTree.node A10K2.u416 (nat_lit 8569736) (nat_lit 14001432233) (nat_lit 0) A10K2.u417 from rfl, allE_node, arows416, irow418, arows417]
  all_goals rfl

theorem atot418 : totK PA10K2 A10K2.u418 = [0, 1525499673796, 6332435899439, 7915215717543, 2737294139111, 220752488982, 0, 0, 0, 0] := by
  rw [show A10K2.u418 = KTree.node A10K2.u416 (nat_lit 8569736) (nat_lit 14001432233) (nat_lit 0) A10K2.u417 from rfl, totK_node, atot416, atot417]
  decide +kernel

theorem arows422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u422 = true := by
  rw [show A10K2.u422 = KTree.node A10K2.u420 (nat_lit 8589676) (nat_lit 11283218440) (nat_lit 0) A10K2.u421 from rfl, allE_node, arows420, irow422, arows421]
  all_goals rfl

theorem atot422 : totK PA10K2 A10K2.u422 = [1313649368211, 5549134868035, 7810454200212, 4137693024628, 1031816703209, 171719894987, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u422 = KTree.node A10K2.u420 (nat_lit 8589676) (nat_lit 11283218440) (nat_lit 0) A10K2.u421 from rfl, totK_node, atot420, atot421]
  decide +kernel

theorem arows425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u425 = true := by
  rw [show A10K2.u425 = KTree.node A10K2.u423 (nat_lit 8617619) (nat_lit 10647992423) (nat_lit 0) A10K2.u424 from rfl, allE_node, arows423, irow425, arows424]
  all_goals rfl

theorem atot425 : totK PA10K2 A10K2.u425 = [276704929378, 2751684991534, 7413917019831, 7342463271300, 2290954342062, 164071913131, 0, 0, 0, 0] := by
  rw [show A10K2.u425 = KTree.node A10K2.u423 (nat_lit 8617619) (nat_lit 10647992423) (nat_lit 0) A10K2.u424 from rfl, totK_node, atot423, atot424]
  decide +kernel

theorem arows430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u430 = true := by
  rw [show A10K2.u430 = KTree.node A10K2.u428 (nat_lit 8645851) (nat_lit 9345680493) (nat_lit 0) A10K2.u429 from rfl, allE_node, arows428, irow430, arows429]
  all_goals rfl

theorem atot430 : totK PA10K2 A10K2.u430 = [0, 796458046475, 4351306640610, 8145289180626, 5632767243995, 1176403210133, 42003213862, 0, 0, 0] := by
  rw [show A10K2.u430 = KTree.node A10K2.u428 (nat_lit 8645851) (nat_lit 9345680493) (nat_lit 0) A10K2.u429 from rfl, totK_node, atot428, atot429]
  decide +kernel

theorem arows433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u433 = true := by
  rw [show A10K2.u433 = KTree.node A10K2.u431 (nat_lit 8655237) (nat_lit 5379571226) (nat_lit 0) A10K2.u432 from rfl, allE_node, arows431, irow433, arows432]
  all_goals rfl

theorem atot433 : totK PA10K2 A10K2.u433 = [0, 1311384078388, 5569084237424, 7712830891462, 3873508817767, 714454590157, 56843514394, 0, 0, 0] := by
  rw [show A10K2.u433 = KTree.node A10K2.u431 (nat_lit 8655237) (nat_lit 5379571226) (nat_lit 0) A10K2.u432 from rfl, totK_node, atot431, atot432]
  decide +kernel

theorem arows437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u437 = true := by
  rw [show A10K2.u437 = KTree.node A10K2.u435 (nat_lit 8675876) (nat_lit 12419335735) (nat_lit 0) A10K2.u436 from rfl, allE_node, arows435, irow437, arows436]
  all_goals rfl

theorem atot437 : totK PA10K2 A10K2.u437 = [0, 977401383692, 5061582192769, 8408338769892, 4571424549170, 615595380760, 12558367923, 0, 0, 0] := by
  rw [show A10K2.u437 = KTree.node A10K2.u435 (nat_lit 8675876) (nat_lit 12419335735) (nat_lit 0) A10K2.u436 from rfl, totK_node, atot435, atot436]
  decide +kernel

theorem arows440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u440 = true := by
  rw [show A10K2.u440 = KTree.node A10K2.u438 (nat_lit 8687685) (nat_lit 6037852959) (nat_lit 0) A10K2.u439 from rfl, allE_node, arows438, irow440, arows439]
  all_goals rfl

theorem atot440 : totK PA10K2 A10K2.u440 = [0, 0, 1300182851933, 5547429016636, 7643394864539, 3714666871708, 629547298947, 30605747850, 0, 0] := by
  rw [show A10K2.u440 = KTree.node A10K2.u438 (nat_lit 8687685) (nat_lit 6037852959) (nat_lit 0) A10K2.u439 from rfl, totK_node, atot438, atot439]
  decide +kernel

theorem arows447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u447 = true := by
  rw [show A10K2.u447 = KTree.node A10K2.u445 (nat_lit 8708620) (nat_lit 10694778644) (nat_lit 0) A10K2.u446 from rfl, allE_node, arows445, irow447, arows446]
  all_goals rfl

theorem atot447 : totK PA10K2 A10K2.u447 = [0, 582795608404, 3092673615053, 6557784038001, 6360857078794, 2208750810671, 245932583563, 5528811039, 0, 0] := by
  rw [show A10K2.u447 = KTree.node A10K2.u445 (nat_lit 8708620) (nat_lit 10694778644) (nat_lit 0) A10K2.u446 from rfl, totK_node, atot445, atot446]
  decide +kernel

theorem arows450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u450 = true := by
  rw [show A10K2.u450 = KTree.node A10K2.u448 (nat_lit 8791446) (nat_lit 12274383641) (nat_lit 0) A10K2.u449 from rfl, allE_node, arows448, irow450, arows449]
  all_goals rfl

theorem atot450 : totK PA10K2 A10K2.u450 = [0, 998981145068, 4768137266153, 7791150268153, 4650768008467, 820164186108, 36865889447, 0, 0, 0] := by
  rw [show A10K2.u450 = KTree.node A10K2.u448 (nat_lit 8791446) (nat_lit 12274383641) (nat_lit 0) A10K2.u449 from rfl, totK_node, atot448, atot449]
  decide +kernel

theorem arows454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u454 = true := by
  rw [show A10K2.u454 = KTree.node A10K2.u452 (nat_lit 8804565) (nat_lit 6365199804) (nat_lit 0) A10K2.u453 from rfl, allE_node, arows452, irow454, arows453]
  all_goals rfl

theorem atot454 : totK PA10K2 A10K2.u454 = [0, 532000767695, 3792526736375, 7893222916805, 5426631084151, 1052752938988, 44905858284, 0, 0, 0] := by
  rw [show A10K2.u454 = KTree.node A10K2.u452 (nat_lit 8804565) (nat_lit 6365199804) (nat_lit 0) A10K2.u453 from rfl, totK_node, atot452, atot453]
  decide +kernel

theorem arows457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u457 = true := by
  rw [show A10K2.u457 = KTree.node A10K2.u455 (nat_lit 8833570) (nat_lit 8816488069) (nat_lit 0) A10K2.u456 from rfl, allE_node, arows455, irow457, arows456]
  all_goals rfl

theorem atot457 : totK PA10K2 A10K2.u457 = [0, 510277227219, 2912501453322, 6564932045410, 6326249839866, 2094334199811, 229167355618, 5676195732, 0, 0] := by
  rw [show A10K2.u457 = KTree.node A10K2.u455 (nat_lit 8833570) (nat_lit 8816488069) (nat_lit 0) A10K2.u456 from rfl, totK_node, atot455, atot456]
  decide +kernel

theorem arows462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u462 = true := by
  rw [show A10K2.u462 = KTree.node A10K2.u460 (nat_lit 8872049) (nat_lit 8334353339) (nat_lit 0) A10K2.u461 from rfl, allE_node, arows460, irow462, arows461]
  all_goals rfl

theorem atot462 : totK PA10K2 A10K2.u462 = [0, 1091343973926, 5243955327026, 8412896606431, 4661039951435, 788785012456, 32166696177, 0, 0, 0] := by
  rw [show A10K2.u462 = KTree.node A10K2.u460 (nat_lit 8872049) (nat_lit 8334353339) (nat_lit 0) A10K2.u461 from rfl, totK_node, atot460, atot461]
  decide +kernel

theorem arows465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u465 = true := by
  rw [show A10K2.u465 = KTree.node A10K2.u463 (nat_lit 8989220) (nat_lit 13394116009) (nat_lit 0) A10K2.u464 from rfl, allE_node, arows463, irow465, arows464]
  all_goals rfl

theorem atot465 : totK PA10K2 A10K2.u465 = [843291061595, 3818455784198, 6304966957030, 5185681128496, 2733247037755, 757023509610, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u465 = KTree.node A10K2.u463 (nat_lit 8989220) (nat_lit 13394116009) (nat_lit 0) A10K2.u464 from rfl, totK_node, atot463, atot464]
  decide +kernel

theorem arows469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u469 = true := by
  rw [show A10K2.u469 = KTree.node A10K2.u467 (nat_lit 9000176) (nat_lit 6149599454) (nat_lit 0) A10K2.u468 from rfl, allE_node, arows467, irow469, arows468]
  all_goals rfl

theorem atot469 : totK PA10K2 A10K2.u469 = [1342370522690, 5835290283069, 8070671638119, 3706719149705, 448180459361, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u469 = KTree.node A10K2.u467 (nat_lit 9000176) (nat_lit 6149599454) (nat_lit 0) A10K2.u468 from rfl, totK_node, atot467, atot468]
  decide +kernel

theorem arows472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u472 = true := by
  rw [show A10K2.u472 = KTree.node A10K2.u470 (nat_lit 9021733) (nat_lit 7473897057) (nat_lit 0) A10K2.u471 from rfl, allE_node, arows470, irow472, arows471]
  all_goals rfl

theorem atot472 : totK PA10K2 A10K2.u472 = [0, 1361715651222, 5870730826290, 7870610536060, 3765506781603, 621383698807, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u472 = KTree.node A10K2.u470 (nat_lit 9021733) (nat_lit 7473897057) (nat_lit 0) A10K2.u471 from rfl, totK_node, atot470, atot471]
  decide +kernel

theorem arows478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u478 = true := by
  rw [show A10K2.u478 = KTree.node A10K2.u476 (nat_lit 9032983) (nat_lit 9683524540) (nat_lit 0) A10K2.u477 from rfl, allE_node, arows476, irow478, arows477]
  all_goals rfl

theorem atot478 : totK PA10K2 A10K2.u478 = [110684666881, 1564673551490, 5847504381074, 7937951622847, 3438505448867, 366557391284, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u478 = KTree.node A10K2.u476 (nat_lit 9032983) (nat_lit 9683524540) (nat_lit 0) A10K2.u477 from rfl, totK_node, atot476, atot477]
  decide +kernel

theorem arows481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u481 = true := by
  rw [show A10K2.u481 = KTree.node A10K2.u479 (nat_lit 9050902) (nat_lit 1803137715) (nat_lit 0) A10K2.u480 from rfl, allE_node, arows479, irow481, arows480]
  all_goals rfl

theorem atot481 : totK PA10K2 A10K2.u481 = [1219541409650, 5470578234506, 7936776358566, 4030552893706, 669908589633, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u481 = KTree.node A10K2.u479 (nat_lit 9050902) (nat_lit 1803137715) (nat_lit 0) A10K2.u480 from rfl, totK_node, atot479, atot480]
  decide +kernel

theorem arows485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u485 = true := by
  rw [show A10K2.u485 = KTree.node A10K2.u483 (nat_lit 9062248) (nat_lit 7458359889) (nat_lit 0) A10K2.u484 from rfl, allE_node, arows483, irow485, arows484]
  all_goals rfl

theorem atot485 : totK PA10K2 A10K2.u485 = [818722742184, 4503475764500, 7891303284793, 4817332975562, 868574047968, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u485 = KTree.node A10K2.u483 (nat_lit 9062248) (nat_lit 7458359889) (nat_lit 0) A10K2.u484 from rfl, totK_node, atot483, atot484]
  decide +kernel

theorem arows488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u488 = true := by
  rw [show A10K2.u488 = KTree.node A10K2.u486 (nat_lit 9088150) (nat_lit 15201631928) (nat_lit 0) A10K2.u487 from rfl, allE_node, arows486, irow488, arows487]
  all_goals rfl

theorem atot488 : totK PA10K2 A10K2.u488 = [0, 1895698906234, 7201105773538, 7793772712812, 2145117331002, 127955765456, 0, 0, 0, 0] := by
  rw [show A10K2.u488 = KTree.node A10K2.u486 (nat_lit 9088150) (nat_lit 15201631928) (nat_lit 0) A10K2.u487 from rfl, totK_node, atot486, atot487]
  decide +kernel

theorem arows493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u493 = true := by
  rw [show A10K2.u493 = KTree.node A10K2.u491 (nat_lit 9251341) (nat_lit 5444536176) (nat_lit 0) A10K2.u492 from rfl, allE_node, arows491, irow493, arows492]
  all_goals rfl

theorem atot493 : totK PA10K2 A10K2.u493 = [0, 840796871205, 4564978242163, 8012232833046, 4703728712162, 866510774540, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u493 = KTree.node A10K2.u491 (nat_lit 9251341) (nat_lit 5444536176) (nat_lit 0) A10K2.u492 from rfl, totK_node, atot491, atot492]
  decide +kernel

theorem arows496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u496 = true := by
  rw [show A10K2.u496 = KTree.node A10K2.u494 (nat_lit 9262372) (nat_lit 13973624068) (nat_lit 0) A10K2.u495 from rfl, allE_node, arows494, irow496, arows495]
  all_goals rfl

theorem atot496 : totK PA10K2 A10K2.u496 = [0, 1340604971947, 5860609484328, 8095110979090, 3622706482353, 390502069369, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u496 = KTree.node A10K2.u494 (nat_lit 9262372) (nat_lit 13973624068) (nat_lit 0) A10K2.u495 from rfl, totK_node, atot494, atot495]
  decide +kernel

theorem arows500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u500 = true := by
  rw [show A10K2.u500 = KTree.node A10K2.u498 (nat_lit 9284141) (nat_lit 6346313702) (nat_lit 0) A10K2.u499 from rfl, allE_node, arows498, irow500, arows499]
  all_goals rfl

theorem atot500 : totK PA10K2 A10K2.u500 = [0, 0, 1314667762869, 5765910079763, 7905944651911, 3690454344437, 605684852121, 31018567651, 0, 0] := by
  rw [show A10K2.u500 = KTree.node A10K2.u498 (nat_lit 9284141) (nat_lit 6346313702) (nat_lit 0) A10K2.u499 from rfl, totK_node, atot498, atot499]
  decide +kernel

theorem arows503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u503 = true := by
  rw [show A10K2.u503 = KTree.node A10K2.u501 (nat_lit 9295920) (nat_lit 7830459814) (nat_lit 0) A10K2.u502 from rfl, allE_node, arows501, irow503, arows502]
  all_goals rfl

theorem atot503 : totK PA10K2 A10K2.u503 = [0, 277343490675, 2179229129805, 6271201456902, 7274721587384, 2788565952142, 306401515452, 5685526223, 0, 0] := by
  rw [show A10K2.u503 = KTree.node A10K2.u501 (nat_lit 9295920) (nat_lit 7830459814) (nat_lit 0) A10K2.u502 from rfl, totK_node, atot501, atot502]
  decide +kernel

theorem arows513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u513 = true := by
  rw [show A10K2.u513 = KTree.node A10K2.u511 (nat_lit 9316140) (nat_lit 13098636310) (nat_lit 0) A10K2.u512 from rfl, allE_node, arows511, irow513, arows512]
  all_goals rfl

theorem atot513 : totK PA10K2 A10K2.u513 = [0, 1052517307383, 5137195349618, 8085840976807, 4230316631237, 660162481890, 31195026185, 0, 0, 0] := by
  rw [show A10K2.u513 = KTree.node A10K2.u511 (nat_lit 9316140) (nat_lit 13098636310) (nat_lit 0) A10K2.u512 from rfl, totK_node, atot511, atot512]
  decide +kernel

theorem arows516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u516 = true := by
  rw [show A10K2.u516 = KTree.node A10K2.u514 (nat_lit 9325408) (nat_lit 11307087167) (nat_lit 0) A10K2.u515 from rfl, allE_node, arows514, irow516, arows515]
  all_goals rfl

theorem atot516 : totK PA10K2 A10K2.u516 = [0, 818358102331, 4530298207586, 8028434830716, 4760180889358, 734898633135, 17774690686, 0, 0, 0] := by
  rw [show A10K2.u516 = KTree.node A10K2.u514 (nat_lit 9325408) (nat_lit 11307087167) (nat_lit 0) A10K2.u515 from rfl, totK_node, atot514, atot515]
  decide +kernel

theorem arows520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u520 = true := by
  rw [show A10K2.u520 = KTree.node A10K2.u518 (nat_lit 9356044) (nat_lit 11917901536) (nat_lit 0) A10K2.u519 from rfl, allE_node, arows518, irow520, arows519]
  all_goals rfl

theorem atot520 : totK PA10K2 A10K2.u520 = [0, 0, 1579582655057, 6708972990557, 8060359718614, 2310380310878, 146015260491, 0, 0, 0] := by
  rw [show A10K2.u520 = KTree.node A10K2.u518 (nat_lit 9356044) (nat_lit 11917901536) (nat_lit 0) A10K2.u519 from rfl, totK_node, atot518, atot519]
  decide +kernel

theorem arows523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u523 = true := by
  rw [show A10K2.u523 = KTree.node A10K2.u521 (nat_lit 9441378) (nat_lit 6092548328) (nat_lit 0) A10K2.u522 from rfl, allE_node, arows521, irow523, arows522]
  all_goals rfl

theorem atot523 : totK PA10K2 A10K2.u523 = [1257633742337, 5132856533757, 7221895981903, 3760710473145, 975494139720, 570040362069, 144939828619, 6239673734, 0, 0] := by
  rw [show A10K2.u523 = KTree.node A10K2.u521 (nat_lit 9441378) (nat_lit 6092548328) (nat_lit 0) A10K2.u522 from rfl, totK_node, atot521, atot522]
  decide +kernel

theorem arows528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u528 = true := by
  rw [show A10K2.u528 = KTree.node A10K2.u526 (nat_lit 9461838) (nat_lit 10904956324) (nat_lit 0) A10K2.u527 from rfl, allE_node, arows526, irow528, arows527]
  all_goals rfl

theorem atot528 : totK PA10K2 A10K2.u528 = [836330893060, 4693551633240, 8167880730138, 4984213462149, 991776382830, 55874098956, 0, 0, 0, 0] := by
  rw [show A10K2.u528 = KTree.node A10K2.u526 (nat_lit 9461838) (nat_lit 10904956324) (nat_lit 0) A10K2.u527 from rfl, totK_node, atot526, atot527]
  decide +kernel

theorem arows531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u531 = true := by
  rw [show A10K2.u531 = KTree.node A10K2.u529 (nat_lit 9474678) (nat_lit 13466153745) (nat_lit 0) A10K2.u530 from rfl, allE_node, arows529, irow531, arows530]
  all_goals rfl

theorem atot531 : totK PA10K2 A10K2.u531 = [0, 1361927450066, 5656420845085, 7657170338888, 3650937877849, 612634129681, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u531 = KTree.node A10K2.u529 (nat_lit 9474678) (nat_lit 13466153745) (nat_lit 0) A10K2.u530 from rfl, totK_node, atot529, atot530]
  decide +kernel

theorem arows535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u535 = true := by
  rw [show A10K2.u535 = KTree.node A10K2.u533 (nat_lit 9497719) (nat_lit 14652227679) (nat_lit 0) A10K2.u534 from rfl, allE_node, arows533, irow535, arows534]
  all_goals rfl

theorem atot535 : totK PA10K2 A10K2.u535 = [763974328874, 3518863110802, 6527997796760, 6074112749032, 2310557796646, 263066729890, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u535 = KTree.node A10K2.u533 (nat_lit 9497719) (nat_lit 14652227679) (nat_lit 0) A10K2.u534 from rfl, totK_node, atot533, atot534]
  decide +kernel

theorem arows538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u538 = true := by
  rw [show A10K2.u538 = KTree.node A10K2.u536 (nat_lit 9520786) (nat_lit 15737539539) (nat_lit 0) A10K2.u537 from rfl, allE_node, arows536, irow538, arows537]
  all_goals rfl

theorem atot538 : totK PA10K2 A10K2.u538 = [891506409665, 4518467134308, 7802822190370, 4888582698909, 895124936190, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u538 = KTree.node A10K2.u536 (nat_lit 9520786) (nat_lit 15737539539) (nat_lit 0) A10K2.u537 from rfl, totK_node, atot536, atot537]
  decide +kernel

theorem arows544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u544 = true := by
  rw [show A10K2.u544 = KTree.node A10K2.u542 (nat_lit 9546519) (nat_lit 7574462884) (nat_lit 0) A10K2.u543 from rfl, allE_node, arows542, irow544, arows543]
  all_goals rfl

theorem atot544 : totK PA10K2 A10K2.u544 = [157101129727, 1956346905211, 5999319191149, 7092630818397, 3449914265861, 611234778886, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u544 = KTree.node A10K2.u542 (nat_lit 9546519) (nat_lit 7574462884) (nat_lit 0) A10K2.u543 from rfl, totK_node, atot542, atot543]
  decide +kernel

theorem arows547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u547 = true := by
  rw [show A10K2.u547 = KTree.node A10K2.u545 (nat_lit 9558244) (nat_lit 13543310126) (nat_lit 0) A10K2.u546 from rfl, allE_node, arows545, irow547, arows546]
  all_goals rfl

theorem atot547 : totK PA10K2 A10K2.u547 = [578044150334, 2945389613032, 6124969141296, 6421984178893, 2587647196569, 277152459832, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u547 = KTree.node A10K2.u545 (nat_lit 9558244) (nat_lit 13543310126) (nat_lit 0) A10K2.u546 from rfl, totK_node, atot545, atot546]
  decide +kernel

theorem arows551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u551 = true := by
  rw [show A10K2.u551 = KTree.node A10K2.u549 (nat_lit 9577942) (nat_lit 14522962693) (nat_lit 0) A10K2.u550 from rfl, allE_node, arows549, irow551, arows550]
  all_goals rfl

theorem atot551 : totK PA10K2 A10K2.u551 = [868381343590, 4456029940904, 7672031606387, 4848288784397, 992160284966, 56566207178, 0, 0, 0, 0] := by
  rw [show A10K2.u551 = KTree.node A10K2.u549 (nat_lit 9577942) (nat_lit 14522962693) (nat_lit 0) A10K2.u550 from rfl, totK_node, atot549, atot550]
  decide +kernel

theorem arows554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u554 = true := by
  rw [show A10K2.u554 = KTree.node A10K2.u552 (nat_lit 9587361) (nat_lit 7859361199) (nat_lit 0) A10K2.u553 from rfl, allE_node, arows552, irow554, arows553]
  all_goals rfl

theorem atot554 : totK PA10K2 A10K2.u554 = [849905977144, 4488727642082, 7843507909578, 4834217847337, 872090027888, 38021971230, 0, 0, 0, 0] := by
  rw [show A10K2.u554 = KTree.node A10K2.u552 (nat_lit 9587361) (nat_lit 7859361199) (nat_lit 0) A10K2.u553 from rfl, totK_node, atot552, atot553]
  decide +kernel

theorem arows559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u559 = true := by
  rw [show A10K2.u559 = KTree.node A10K2.u557 (nat_lit 9612510) (nat_lit 11333817657) (nat_lit 0) A10K2.u558 from rfl, allE_node, arows557, irow559, arows558]
  all_goals rfl

theorem atot559 : totK PA10K2 A10K2.u559 = [0, 1889221568681, 7110934272622, 7647286280458, 2096028760829, 128630078389, 0, 0, 0, 0] := by
  rw [show A10K2.u559 = KTree.node A10K2.u557 (nat_lit 9612510) (nat_lit 11333817657) (nat_lit 0) A10K2.u558 from rfl, totK_node, atot557, atot558]
  decide +kernel

theorem arows562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u562 = true := by
  rw [show A10K2.u562 = KTree.node A10K2.u560 (nat_lit 9702151) (nat_lit 7527947976) (nat_lit 0) A10K2.u561 from rfl, allE_node, arows560, irow562, arows561]
  all_goals rfl

theorem atot562 : totK PA10K2 A10K2.u562 = [0, 875998210603, 4581699709718, 7985163770201, 4683731410154, 839802996670, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u562 = KTree.node A10K2.u560 (nat_lit 9702151) (nat_lit 7527947976) (nat_lit 0) A10K2.u561 from rfl, totK_node, atot560, atot561]
  decide +kernel

theorem arows566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u566 = true := by
  rw [show A10K2.u566 = KTree.node A10K2.u564 (nat_lit 9721115) (nat_lit 9838213930) (nat_lit 0) A10K2.u565 from rfl, allE_node, arows564, irow566, arows565]
  all_goals rfl

theorem atot566 : totK PA10K2 A10K2.u566 = [0, 1202012893553, 5629816559559, 8189026338938, 3824831746183, 465674433933, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u566 = KTree.node A10K2.u564 (nat_lit 9721115) (nat_lit 9838213930) (nat_lit 0) A10K2.u565 from rfl, totK_node, atot564, atot565]
  decide +kernel

theorem arows569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u569 = true := by
  rw [show A10K2.u569 = KTree.node A10K2.u567 (nat_lit 9778359) (nat_lit 14401140337) (nat_lit 0) A10K2.u568 from rfl, allE_node, arows567, irow569, arows568]
  all_goals rfl

theorem atot569 : totK PA10K2 A10K2.u569 = [0, 1245044792977, 5236723967397, 7581154830392, 4388747091617, 841980543134, 38305921858, 0, 0, 0] := by
  rw [show A10K2.u569 = KTree.node A10K2.u567 (nat_lit 9778359) (nat_lit 14401140337) (nat_lit 0) A10K2.u568 from rfl, totK_node, atot567, atot568]
  decide +kernel

theorem arows576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u576 = true := by
  rw [show A10K2.u576 = KTree.node A10K2.u574 (nat_lit 9790688) (nat_lit 3610758241) (nat_lit 0) A10K2.u575 from rfl, allE_node, arows574, irow576, arows575]
  all_goals rfl

theorem atot576 : totK PA10K2 A10K2.u576 = [0, 1141954140530, 5415789412886, 8037865072691, 3954807283749, 568013272004, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u576 = KTree.node A10K2.u574 (nat_lit 9790688) (nat_lit 3610758241) (nat_lit 0) A10K2.u575 from rfl, totK_node, atot574, atot575]
  decide +kernel

theorem arows579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u579 = true := by
  rw [show A10K2.u579 = KTree.node A10K2.u577 (nat_lit 9840091) (nat_lit 6870203376) (nat_lit 0) A10K2.u578 from rfl, allE_node, arows577, irow579, arows578]
  all_goals rfl

theorem atot579 : totK PA10K2 A10K2.u579 = [0, 867383163940, 4531284843872, 7837444592729, 4578294911052, 817900900181, 55044112671, 0, 0, 0] := by
  rw [show A10K2.u579 = KTree.node A10K2.u577 (nat_lit 9840091) (nat_lit 6870203376) (nat_lit 0) A10K2.u578 from rfl, totK_node, atot577, atot578]
  decide +kernel

theorem arows583 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u583 = true := by
  rw [show A10K2.u583 = KTree.node A10K2.u581 (nat_lit 9849608) (nat_lit 12335141594) (nat_lit 0) A10K2.u582 from rfl, allE_node, arows581, irow583, arows582]
  all_goals rfl

theorem atot583 : totK PA10K2 A10K2.u583 = [0, 846685665495, 4508982286478, 7805308224953, 4639642383948, 805438059442, 37227445626, 0, 0, 0] := by
  rw [show A10K2.u583 = KTree.node A10K2.u581 (nat_lit 9849608) (nat_lit 12335141594) (nat_lit 0) A10K2.u582 from rfl, totK_node, atot581, atot582]
  decide +kernel

theorem arows586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u586 = true := by
  rw [show A10K2.u586 = KTree.node A10K2.u584 (nat_lit 9879843) (nat_lit 9298980690) (nat_lit 0) A10K2.u585 from rfl, allE_node, arows584, irow586, arows585]
  all_goals rfl

theorem atot586 : totK PA10K2 A10K2.u586 = [0, 0, 1800605000782, 6950142747789, 7449026116238, 2095194071879, 146499614604, 0, 0, 0] := by
  rw [show A10K2.u586 = KTree.node A10K2.u584 (nat_lit 9879843) (nat_lit 9298980690) (nat_lit 0) A10K2.u585 from rfl, totK_node, atot584, atot585]
  decide +kernel

theorem arows591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u591 = true := by
  rw [show A10K2.u591 = KTree.node A10K2.u589 (nat_lit 10489384) (nat_lit 12340726659) (nat_lit 0) A10K2.u590 from rfl, allE_node, arows589, irow591, arows590]
  all_goals rfl

theorem atot591 : totK PA10K2 A10K2.u591 = [0, 1149846794743, 4789880211523, 6973376677441, 4562452209073, 1488751534655, 238101393080, 6354482628, 0, 0] := by
  rw [show A10K2.u591 = KTree.node A10K2.u589 (nat_lit 10489384) (nat_lit 12340726659) (nat_lit 0) A10K2.u590 from rfl, totK_node, atot589, atot590]
  decide +kernel

theorem arows594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u594 = true := by
  rw [show A10K2.u594 = KTree.node A10K2.u592 (nat_lit 10508630) (nat_lit 5591778599) (nat_lit 0) A10K2.u593 from rfl, allE_node, arows592, irow594, arows593]
  all_goals rfl

theorem atot594 : totK PA10K2 A10K2.u594 = [0, 1143099648562, 5462398524120, 8298412591848, 3988842874013, 484416703331, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u594 = KTree.node A10K2.u592 (nat_lit 10508630) (nat_lit 5591778599) (nat_lit 0) A10K2.u593 from rfl, totK_node, atot592, atot593]
  decide +kernel

theorem arows598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u598 = true := by
  rw [show A10K2.u598 = KTree.node A10K2.u596 (nat_lit 10521367) (nat_lit 1637620965) (nat_lit 0) A10K2.u597 from rfl, allE_node, arows596, irow598, arows597]
  all_goals rfl

theorem atot598 : totK PA10K2 A10K2.u598 = [0, 0, 1289230959521, 5660552010230, 8049051832959, 3786871043321, 621387343394, 30650496230, 0, 0] := by
  rw [show A10K2.u598 = KTree.node A10K2.u596 (nat_lit 10521367) (nat_lit 1637620965) (nat_lit 0) A10K2.u597 from rfl, totK_node, atot596, atot597]
  decide +kernel

theorem arows601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u601 = true := by
  rw [show A10K2.u601 = KTree.node A10K2.u599 (nat_lit 10541160) (nat_lit 11384882569) (nat_lit 0) A10K2.u600 from rfl, allE_node, arows599, irow601, arows600]
  all_goals rfl

theorem atot601 : totK PA10K2 A10K2.u601 = [0, 304661711030, 2132612926913, 6236678399534, 7537754259425, 2820508856252, 280486631259, 5546304973, 0, 0] := by
  rw [show A10K2.u601 = KTree.node A10K2.u599 (nat_lit 10541160) (nat_lit 11384882569) (nat_lit 0) A10K2.u600 from rfl, totK_node, atot599, atot600]
  decide +kernel

theorem arows607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u607 = true := by
  rw [show A10K2.u607 = KTree.node A10K2.u605 (nat_lit 10623122) (nat_lit 13943055236) (nat_lit 0) A10K2.u606 from rfl, allE_node, arows605, irow607, arows606]
  all_goals rfl

theorem atot607 : totK PA10K2 A10K2.u607 = [0, 1000353587425, 5031265954742, 8047411479510, 4372621900635, 727262065903, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u607 = KTree.node A10K2.u605 (nat_lit 10623122) (nat_lit 13943055236) (nat_lit 0) A10K2.u606 from rfl, totK_node, atot605, atot606]
  decide +kernel

theorem arows610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u610 = true := by
  rw [show A10K2.u610 = KTree.node A10K2.u608 (nat_lit 10635525) (nat_lit 7040787894) (nat_lit 0) A10K2.u609 from rfl, allE_node, arows608, irow610, arows609]
  all_goals rfl

theorem atot610 : totK PA10K2 A10K2.u610 = [0, 809888342482, 4326129414030, 7632907387335, 4870616775852, 957201418890, 57935449832, 0, 0, 0] := by
  rw [show A10K2.u610 = KTree.node A10K2.u608 (nat_lit 10635525) (nat_lit 7040787894) (nat_lit 0) A10K2.u609 from rfl, totK_node, atot608, atot609]
  decide +kernel

theorem arows614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u614 = true := by
  rw [show A10K2.u614 = KTree.node A10K2.u612 (nat_lit 10660704) (nat_lit 10829914066) (nat_lit 0) A10K2.u613 from rfl, allE_node, arows612, irow614, arows613]
  all_goals rfl

theorem atot614 : totK PA10K2 A10K2.u614 = [0, 0, 1803682253502, 7000592973358, 7744765072065, 2149280954520, 133084055132, 0, 0, 0] := by
  rw [show A10K2.u614 = KTree.node A10K2.u612 (nat_lit 10660704) (nat_lit 10829914066) (nat_lit 0) A10K2.u613 from rfl, totK_node, atot612, atot613]
  decide +kernel

theorem arows617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u617 = true := by
  rw [show A10K2.u617 = KTree.node A10K2.u615 (nat_lit 10685939) (nat_lit 8383953349) (nat_lit 0) A10K2.u616 from rfl, allE_node, arows615, irow617, arows616]
  all_goals rfl

theorem atot617 : totK PA10K2 A10K2.u617 = [0, 1095933414401, 4638787689967, 7003410480258, 4852597920603, 1739210176043, 264339259141, 6354482628, 0, 0] := by
  rw [show A10K2.u617 = KTree.node A10K2.u615 (nat_lit 10685939) (nat_lit 8383953349) (nat_lit 0) A10K2.u616 from rfl, totK_node, atot615, atot616]
  decide +kernel

theorem arows622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u622 = true := by
  rw [show A10K2.u622 = KTree.node A10K2.u620 (nat_lit 10712786) (nat_lit 15247591075) (nat_lit 0) A10K2.u621 from rfl, allE_node, arows620, irow622, arows621]
  all_goals rfl

theorem atot622 : totK PA10K2 A10K2.u622 = [0, 509805898549, 3655754914892, 8018447577980, 6405333289165, 1594828781016, 93806011435, 0, 0, 0] := by
  rw [show A10K2.u622 = KTree.node A10K2.u620 (nat_lit 10712786) (nat_lit 15247591075) (nat_lit 0) A10K2.u621 from rfl, totK_node, atot620, atot621]
  decide +kernel

theorem arows625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u625 = true := by
  rw [show A10K2.u625 = KTree.node A10K2.u623 (nat_lit 10741169) (nat_lit 7967396626) (nat_lit 0) A10K2.u624 from rfl, allE_node, arows623, irow625, arows624]
  all_goals rfl

theorem atot625 : totK PA10K2 A10K2.u625 = [0, 582869944845, 2887217197186, 6201351899380, 6901833520690, 3008417559311, 360995370117, 6904928264, 0, 0] := by
  rw [show A10K2.u625 = KTree.node A10K2.u623 (nat_lit 10741169) (nat_lit 7967396626) (nat_lit 0) A10K2.u624 from rfl, totK_node, atot623, atot624]
  decide +kernel

theorem arows629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u629 = true := by
  rw [show A10K2.u629 = KTree.node A10K2.u627 (nat_lit 11091410) (nat_lit 15196470988) (nat_lit 0) A10K2.u628 from rfl, allE_node, arows627, irow629, arows628]
  all_goals rfl

theorem atot629 : totK PA10K2 A10K2.u629 = [0, 1005546757754, 4929405947038, 7970083153228, 4530642800320, 740581560184, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u629 = KTree.node A10K2.u627 (nat_lit 11091410) (nat_lit 15196470988) (nat_lit 0) A10K2.u628 from rfl, totK_node, atot627, atot628]
  decide +kernel

theorem arows632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u632 = true := by
  rw [show A10K2.u632 = KTree.node A10K2.u630 (nat_lit 11105570) (nat_lit 13664070545) (nat_lit 0) A10K2.u631 from rfl, allE_node, arows630, irow632, arows631]
  all_goals rfl

theorem atot632 : totK PA10K2 A10K2.u632 = [0, 595393228060, 3712579504796, 7884594489882, 6117204687247, 1452230202581, 74913470744, 0, 0, 0] := by
  rw [show A10K2.u632 = KTree.node A10K2.u630 (nat_lit 11105570) (nat_lit 13664070545) (nat_lit 0) A10K2.u631 from rfl, totK_node, atot630, atot631]
  decide +kernel

theorem arows640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u640 = true := by
  rw [show A10K2.u640 = KTree.node A10K2.u638 (nat_lit 11124182) (nat_lit 15637030661) (nat_lit 0) A10K2.u639 from rfl, allE_node, arows638, irow640, arows639]
  all_goals rfl

theorem atot640 : totK PA10K2 A10K2.u640 = [0, 0, 1004555891412, 5114752471149, 8088107754604, 4076357334026, 650622436232, 31082886609, 0, 0] := by
  rw [show A10K2.u640 = KTree.node A10K2.u638 (nat_lit 11124182) (nat_lit 15637030661) (nat_lit 0) A10K2.u639 from rfl, totK_node, atot638, atot639]
  decide +kernel

theorem arows643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u643 = true := by
  rw [show A10K2.u643 = KTree.node A10K2.u641 (nat_lit 11141637) (nat_lit 6371258804) (nat_lit 0) A10K2.u642 from rfl, allE_node, arows641, irow643, arows642]
  all_goals rfl

theorem atot643 : totK PA10K2 A10K2.u643 = [0, 771637207475, 3598853262679, 6688118799223, 5794943252605, 2119345844738, 246959121832, 6121173289, 0, 0] := by
  rw [show A10K2.u643 = KTree.node A10K2.u641 (nat_lit 11141637) (nat_lit 6371258804) (nat_lit 0) A10K2.u642 from rfl, totK_node, atot641, atot642]
  decide +kernel

theorem arows647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u647 = true := by
  rw [show A10K2.u647 = KTree.node A10K2.u645 (nat_lit 11155468) (nat_lit 11729574452) (nat_lit 0) A10K2.u646 from rfl, allE_node, arows645, irow647, arows646]
  all_goals rfl

theorem atot647 : totK PA10K2 A10K2.u647 = [0, 1259758697716, 5465485191079, 7733329716351, 4067302797427, 694769911111, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u647 = KTree.node A10K2.u645 (nat_lit 11155468) (nat_lit 11729574452) (nat_lit 0) A10K2.u646 from rfl, totK_node, atot645, atot646]
  decide +kernel

theorem arows650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u650 = true := by
  rw [show A10K2.u650 = KTree.node A10K2.u648 (nat_lit 11174753) (nat_lit 8999753644) (nat_lit 0) A10K2.u649 from rfl, allE_node, arows648, irow650, arows649]
  all_goals rfl

theorem atot650 : totK PA10K2 A10K2.u650 = [0, 112111361307, 2767914469248, 7972639707179, 6684602502025, 1455765449501, 70383685680, 0, 0, 0] := by
  rw [show A10K2.u650 = KTree.node A10K2.u648 (nat_lit 11174753) (nat_lit 8999753644) (nat_lit 0) A10K2.u649 from rfl, totK_node, atot648, atot649]
  decide +kernel

theorem arows655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u655 = true := by
  rw [show A10K2.u655 = KTree.node A10K2.u653 (nat_lit 11195554) (nat_lit 14377112747) (nat_lit 0) A10K2.u654 from rfl, allE_node, arows653, irow655, arows654]
  all_goals rfl

theorem atot655 : totK PA10K2 A10K2.u655 = [0, 687562120356, 3141755114007, 6079897193176, 6108681751420, 2408004141116, 322913992912, 6354482628, 0, 0] := by
  rw [show A10K2.u655 = KTree.node A10K2.u653 (nat_lit 11195554) (nat_lit 14377112747) (nat_lit 0) A10K2.u654 from rfl, totK_node, atot653, atot654]
  decide +kernel

theorem arows658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u658 = true := by
  rw [show A10K2.u658 = KTree.node A10K2.u656 (nat_lit 11551061) (nat_lit 6864452057) (nat_lit 0) A10K2.u657 from rfl, allE_node, arows656, irow658, arows657]
  all_goals rfl

theorem atot658 : totK PA10K2 A10K2.u658 = [0, 903620819965, 4851862383210, 8103133775255, 4488207594845, 709731344200, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u658 = KTree.node A10K2.u656 (nat_lit 11551061) (nat_lit 6864452057) (nat_lit 0) A10K2.u657 from rfl, totK_node, atot656, atot657]
  decide +kernel

theorem arows662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u662 = true := by
  rw [show A10K2.u662 = KTree.node A10K2.u660 (nat_lit 11566158) (nat_lit 10943930858) (nat_lit 0) A10K2.u661 from rfl, allE_node, arows660, irow662, arows661]
  all_goals rfl

theorem atot662 : totK PA10K2 A10K2.u662 = [0, 500094607715, 3337792800278, 7715183450212, 6530343230457, 1543943072845, 77653406939, 0, 0, 0] := by
  rw [show A10K2.u662 = KTree.node A10K2.u660 (nat_lit 11566158) (nat_lit 10943930858) (nat_lit 0) A10K2.u661 from rfl, totK_node, atot660, atot661]
  decide +kernel

theorem arows665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u665 = true := by
  rw [show A10K2.u665 = KTree.node A10K2.u663 (nat_lit 11585345) (nat_lit 5884814329) (nat_lit 0) A10K2.u664 from rfl, allE_node, arows663, irow665, arows664]
  all_goals rfl

theorem atot665 : totK PA10K2 A10K2.u665 = [0, 0, 1056870025885, 5118507022983, 7882547147074, 3931029079838, 660266964008, 35767183343, 0, 0] := by
  rw [show A10K2.u665 = KTree.node A10K2.u663 (nat_lit 11585345) (nat_lit 5884814329) (nat_lit 0) A10K2.u664 from rfl, totK_node, atot663, atot664]
  decide +kernel

theorem arows671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u671 = true := by
  rw [show A10K2.u671 = KTree.node A10K2.u669 (nat_lit 11612124) (nat_lit 2626563542) (nat_lit 0) A10K2.u670 from rfl, allE_node, arows669, irow671, arows670]
  all_goals rfl

theorem atot671 : totK PA10K2 A10K2.u671 = [0, 1178723396748, 5037472113557, 7608863804170, 4745666390147, 915532943882, 38551227967, 0, 0, 0] := by
  rw [show A10K2.u671 = KTree.node A10K2.u669 (nat_lit 11612124) (nat_lit 2626563542) (nat_lit 0) A10K2.u670 from rfl, totK_node, atot669, atot670]
  decide +kernel

theorem arows674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u674 = true := by
  rw [show A10K2.u674 = KTree.node A10K2.u672 (nat_lit 11623272) (nat_lit 8866611563) (nat_lit 0) A10K2.u673 from rfl, allE_node, arows672, irow674, arows673]
  all_goals rfl

theorem atot674 : totK PA10K2 A10K2.u674 = [0, 632492471053, 4167305730071, 8136345576181, 5162891183630, 967725926377, 39796321239, 0, 0, 0] := by
  rw [show A10K2.u674 = KTree.node A10K2.u672 (nat_lit 11623272) (nat_lit 8866611563) (nat_lit 0) A10K2.u673 from rfl, totK_node, atot672, atot673]
  decide +kernel

theorem arows678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u678 = true := by
  rw [show A10K2.u678 = KTree.node A10K2.u676 (nat_lit 11649572) (nat_lit 13174403988) (nat_lit 0) A10K2.u677 from rfl, allE_node, arows676, irow678, arows677]
  all_goals rfl

theorem atot678 : totK PA10K2 A10K2.u678 = [0, 0, 964275211761, 5203460706774, 8249169161869, 3863365123838, 566887725881, 30647824416, 0, 0] := by
  rw [show A10K2.u678 = KTree.node A10K2.u676 (nat_lit 11649572) (nat_lit 13174403988) (nat_lit 0) A10K2.u677 from rfl, totK_node, atot676, atot677]
  decide +kernel

theorem arows681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u681 = true := by
  rw [show A10K2.u681 = KTree.node A10K2.u679 (nat_lit 11668537) (nat_lit 7281133814) (nat_lit 0) A10K2.u680 from rfl, allE_node, arows679, irow681, arows680]
  all_goals rfl

theorem atot681 : totK PA10K2 A10K2.u681 = [0, 1025773855106, 4578601946088, 7058529922144, 4657738181400, 1424117677885, 193230872200, 6121173289, 0, 0] := by
  rw [show A10K2.u681 = KTree.node A10K2.u679 (nat_lit 11668537) (nat_lit 7281133814) (nat_lit 0) A10K2.u680 from rfl, totK_node, atot679, atot680]
  decide +kernel

theorem arows686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u686 = true := by
  rw [show A10K2.u686 = KTree.node A10K2.u684 (nat_lit 11680403) (nat_lit 10899815526) (nat_lit 0) A10K2.u685 from rfl, allE_node, arows684, irow686, arows685]
  all_goals rfl

theorem atot686 : totK PA10K2 A10K2.u686 = [0, 1265119596279, 5467352952765, 7620860097311, 3820708600323, 616015031941, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u686 = KTree.node A10K2.u684 (nat_lit 11680403) (nat_lit 10899815526) (nat_lit 0) A10K2.u685 from rfl, totK_node, atot684, atot685]
  decide +kernel

theorem arows689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u689 = true := by
  rw [show A10K2.u689 = KTree.node A10K2.u687 (nat_lit 11700484) (nat_lit 13192877467) (nat_lit 0) A10K2.u688 from rfl, allE_node, arows687, irow689, arows688]
  all_goals rfl

theorem atot689 : totK PA10K2 A10K2.u689 = [0, 0, 2282077071058, 7781188083658, 7124006303603, 1564424414778, 77177557509, 0, 0, 0] := by
  rw [show A10K2.u689 = KTree.node A10K2.u687 (nat_lit 11700484) (nat_lit 13192877467) (nat_lit 0) A10K2.u688 from rfl, totK_node, atot687, atot688]
  decide +kernel

theorem arows693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u693 = true := by
  rw [show A10K2.u693 = KTree.node A10K2.u691 (nat_lit 11719095) (nat_lit 7806559005) (nat_lit 0) A10K2.u692 from rfl, allE_node, arows691, irow693, arows692]
  all_goals rfl

theorem atot693 : totK PA10K2 A10K2.u693 = [0, 0, 1503589710815, 6125061835983, 7782529002748, 2939036943491, 354517253208, 6354482628, 0, 0] := by
  rw [show A10K2.u693 = KTree.node A10K2.u691 (nat_lit 11719095) (nat_lit 7806559005) (nat_lit 0) A10K2.u692 from rfl, totK_node, atot691, atot692]
  decide +kernel

theorem arows696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u696 = true := by
  rw [show A10K2.u696 = KTree.node A10K2.u694 (nat_lit 11813366) (nat_lit 13625770833) (nat_lit 0) A10K2.u695 from rfl, allE_node, arows694, irow696, arows695]
  all_goals rfl

theorem atot696 : totK PA10K2 A10K2.u696 = [0, 0, 923461270320, 5036704880257, 8166658867483, 4063039949597, 610851213043, 30388749007, 0, 0] := by
  rw [show A10K2.u696 = KTree.node A10K2.u694 (nat_lit 11813366) (nat_lit 13625770833) (nat_lit 0) A10K2.u695 from rfl, totK_node, atot694, atot695]
  decide +kernel

theorem arows703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u703 = true := by
  rw [show A10K2.u703 = KTree.node A10K2.u701 (nat_lit 11872404) (nat_lit 12714679208) (nat_lit 0) A10K2.u702 from rfl, allE_node, arows701, irow703, arows702]
  all_goals rfl

theorem atot703 : totK PA10K2 A10K2.u703 = [0, 0, 1262578068585, 5409148273146, 7858243200149, 4067689566650, 697747532943, 37371994285, 0, 0] := by
  rw [show A10K2.u703 = KTree.node A10K2.u701 (nat_lit 11872404) (nat_lit 12714679208) (nat_lit 0) A10K2.u702 from rfl, totK_node, atot701, atot702]
  decide +kernel

theorem arows706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u706 = true := by
  rw [show A10K2.u706 = KTree.node A10K2.u704 (nat_lit 11883820) (nat_lit 13378416925) (nat_lit 0) A10K2.u705 from rfl, allE_node, arows704, irow706, arows705]
  all_goals rfl

theorem atot706 : totK PA10K2 A10K2.u706 = [0, 0, 1507222599240, 6073495384845, 7759000072100, 3164707756011, 377297443395, 6354482628, 0, 0] := by
  rw [show A10K2.u706 = KTree.node A10K2.u704 (nat_lit 11883820) (nat_lit 13378416925) (nat_lit 0) A10K2.u705 from rfl, totK_node, atot704, atot705]
  decide +kernel

theorem arows710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u710 = true := by
  rw [show A10K2.u710 = KTree.node A10K2.u708 (nat_lit 11937051) (nat_lit 10058076976) (nat_lit 0) A10K2.u709 from rfl, allE_node, arows708, irow710, arows709]
  all_goals rfl

theorem atot710 : totK PA10K2 A10K2.u710 = [0, 0, 972656282350, 4864642697688, 7706548075656, 4061683585088, 790126725200, 55044112671, 0, 0] := by
  rw [show A10K2.u710 = KTree.node A10K2.u708 (nat_lit 11937051) (nat_lit 10058076976) (nat_lit 0) A10K2.u709 from rfl, totK_node, atot708, atot709]
  decide +kernel

theorem arows713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u713 = true := by
  rw [show A10K2.u713 = KTree.node A10K2.u711 (nat_lit 11946674) (nat_lit 13689995678) (nat_lit 0) A10K2.u712 from rfl, allE_node, arows711, irow713, arows712]
  all_goals rfl

theorem atot713 : totK PA10K2 A10K2.u713 = [0, 0, 840791772954, 4543544925979, 7910868383769, 4459362599485, 783570722963, 37227445626, 0, 0] := by
  rw [show A10K2.u713 = KTree.node A10K2.u711 (nat_lit 11946674) (nat_lit 13689995678) (nat_lit 0) A10K2.u712 from rfl, totK_node, atot711, atot712]
  decide +kernel

theorem arows718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u718 = true := by
  rw [show A10K2.u718 = KTree.node A10K2.u716 (nat_lit 11977161) (nat_lit 5991979091) (nat_lit 0) A10K2.u717 from rfl, allE_node, arows716, irow718, arows717]
  all_goals rfl

theorem atot718 : totK PA10K2 A10K2.u718 = [0, 0, 0, 1794873768619, 6891464277793, 7202484281026, 2188180441937, 165816551152, 0, 0] := by
  rw [show A10K2.u718 = KTree.node A10K2.u716 (nat_lit 11977161) (nat_lit 5991979091) (nat_lit 0) A10K2.u717 from rfl, totK_node, atot716, atot717]
  decide +kernel

theorem arows721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u721 = true := by
  rw [show A10K2.u721 = KTree.node A10K2.u719 (nat_lit 12586718) (nat_lit 10930322017) (nat_lit 0) A10K2.u720 from rfl, allE_node, arows719, irow721, arows720]
  all_goals rfl

theorem atot721 : totK PA10K2 A10K2.u721 = [1151305832182, 4879407166609, 6995706997590, 3769615068986, 783234706563, 738254923438, 737143629413, 187952782646, 6354482628, 0] := by
  rw [show A10K2.u721 = KTree.node A10K2.u719 (nat_lit 12586718) (nat_lit 10930322017) (nat_lit 0) A10K2.u720 from rfl, totK_node, atot719, atot720]
  decide +kernel

theorem arows725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u725 = true := by
  rw [show A10K2.u725 = KTree.node A10K2.u723 (nat_lit 12607922) (nat_lit 12734719087) (nat_lit 0) A10K2.u724 from rfl, allE_node, arows723, irow725, arows724]
  all_goals rfl

theorem atot725 : totK PA10K2 A10K2.u725 = [1149097285407, 5398644955129, 8176573935692, 4207913115618, 608134714557, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u725 = KTree.node A10K2.u723 (nat_lit 12607922) (nat_lit 12734719087) (nat_lit 0) A10K2.u724 from rfl, totK_node, atot723, atot724]
  decide +kernel

theorem arows728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u728 = true := by
  rw [show A10K2.u728 = KTree.node A10K2.u726 (nat_lit 12618525) (nat_lit 5993252933) (nat_lit 0) A10K2.u727 from rfl, allE_node, arows726, irow728, arows727]
  all_goals rfl

theorem atot728 : totK PA10K2 A10K2.u728 = [0, 1279876747291, 5626124514927, 7943837308286, 3871271167389, 627062978780, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u728 = KTree.node A10K2.u726 (nat_lit 12618525) (nat_lit 5993252933) (nat_lit 0) A10K2.u727 from rfl, totK_node, atot726, atot727]
  decide +kernel

theorem arows734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u734 = true := by
  rw [show A10K2.u734 = KTree.node A10K2.u732 (nat_lit 12638734) (nat_lit 6388380166) (nat_lit 0) A10K2.u733 from rfl, allE_node, arows732, irow734, arows733]
  all_goals rfl

theorem atot734 : totK PA10K2 A10K2.u734 = [252491579350, 2042045069047, 6194299024104, 7571711915532, 3013963624891, 308270757212, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u734 = KTree.node A10K2.u732 (nat_lit 12638734) (nat_lit 6388380166) (nat_lit 0) A10K2.u733 from rfl, totK_node, atot732, atot733]
  decide +kernel

theorem arows737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u737 = true := by
  rw [show A10K2.u737 = KTree.node A10K2.u735 (nat_lit 12720184) (nat_lit 14401970788) (nat_lit 0) A10K2.u736 from rfl, allE_node, arows735, irow737, arows736]
  all_goals rfl

theorem atot737 : totK PA10K2 A10K2.u737 = [1282364285031, 5583209853866, 7893604946191, 4045824660115, 677805483591, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u737 = KTree.node A10K2.u735 (nat_lit 12720184) (nat_lit 14401970788) (nat_lit 0) A10K2.u736 from rfl, totK_node, atot735, atot736]
  decide +kernel

theorem arows741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u741 = true := by
  rw [show A10K2.u741 = KTree.node A10K2.u739 (nat_lit 12749056) (nat_lit 14444943766) (nat_lit 0) A10K2.u740 from rfl, allE_node, arows739, irow741, arows740]
  all_goals rfl

theorem atot741 : totK PA10K2 A10K2.u741 = [0, 2456066591116, 7944030730691, 7032057978473, 1665521906013, 95405038122, 0, 0, 0, 0] := by
  rw [show A10K2.u741 = KTree.node A10K2.u739 (nat_lit 12749056) (nat_lit 14444943766) (nat_lit 0) A10K2.u740 from rfl, totK_node, atot739, atot740]
  decide +kernel

theorem arows744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u744 = true := by
  rw [show A10K2.u744 = KTree.node A10K2.u742 (nat_lit 12781921) (nat_lit 8978401492) (nat_lit 0) A10K2.u743 from rfl, allE_node, arows742, irow744, arows743]
  all_goals rfl

theorem atot744 : totK PA10K2 A10K2.u744 = [801349738877, 3667143904127, 6566262342800, 5766119590674, 2189073744494, 296584157553, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u744 = KTree.node A10K2.u742 (nat_lit 12781921) (nat_lit 8978401492) (nat_lit 0) A10K2.u743 from rfl, totK_node, atot742, atot743]
  decide +kernel

theorem arows749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u749 = true := by
  rw [show A10K2.u749 = KTree.node A10K2.u747 (nat_lit 12795285) (nat_lit 4221744202) (nat_lit 0) A10K2.u748 from rfl, allE_node, arows747, irow749, arows748]
  all_goals rfl

theorem atot749 : totK PA10K2 A10K2.u749 = [1420687879820, 5958403057975, 8145543800925, 3894401446512, 546054137346, 19734769798, 0, 0, 0, 0] := by
  rw [show A10K2.u749 = KTree.node A10K2.u747 (nat_lit 12795285) (nat_lit 4221744202) (nat_lit 0) A10K2.u748 from rfl, totK_node, atot747, atot748]
  decide +kernel

theorem arows752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u752 = true := by
  rw [show A10K2.u752 = KTree.node A10K2.u750 (nat_lit 12812864) (nat_lit 15088835041) (nat_lit 0) A10K2.u751 from rfl, allE_node, arows750, irow752, arows751]
  all_goals rfl

theorem atot752 : totK PA10K2 A10K2.u752 = [0, 1550143320731, 6400927075634, 8153994145157, 3301481875029, 373993404549, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u752 = KTree.node A10K2.u750 (nat_lit 12812864) (nat_lit 15088835041) (nat_lit 0) A10K2.u751 from rfl, totK_node, atot750, atot751]
  decide +kernel

theorem arows756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u756 = true := by
  rw [show A10K2.u756 = KTree.node A10K2.u754 (nat_lit 12827763) (nat_lit 6089924588) (nat_lit 0) A10K2.u755 from rfl, allE_node, arows754, irow756, arows755]
  all_goals rfl

theorem atot756 : totK PA10K2 A10K2.u756 = [0, 1418852129352, 5983425669524, 8238827905421, 3825542158306, 433200265720, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u756 = KTree.node A10K2.u754 (nat_lit 12827763) (nat_lit 6089924588) (nat_lit 0) A10K2.u755 from rfl, totK_node, atot754, atot755]
  decide +kernel

theorem arows759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u759 = true := by
  rw [show A10K2.u759 = KTree.node A10K2.u757 (nat_lit 12845518) (nat_lit 14616406979) (nat_lit 0) A10K2.u758 from rfl, allE_node, arows757, irow759, arows758]
  all_goals rfl

theorem atot759 : totK PA10K2 A10K2.u759 = [0, 859381108411, 4307222644743, 7565325010992, 5406610919298, 1310641471846, 81180888921, 0, 0, 0] := by
  rw [show A10K2.u759 = KTree.node A10K2.u757 (nat_lit 12845518) (nat_lit 14616406979) (nat_lit 0) A10K2.u758 from rfl, totK_node, atot757, atot758]
  decide +kernel

theorem arows768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u768 = true := by
  rw [show A10K2.u768 = KTree.node A10K2.u766 (nat_lit 12864164) (nat_lit 13693685982) (nat_lit 0) A10K2.u767 from rfl, allE_node, arows766, irow768, arows767]
  all_goals rfl

theorem atot768 : totK PA10K2 A10K2.u768 = [0, 1233269050197, 5410851627040, 8072669888138, 3984816560278, 510199478535, 16465930986, 0, 0, 0] := by
  rw [show A10K2.u768 = KTree.node A10K2.u766 (nat_lit 12864164) (nat_lit 13693685982) (nat_lit 0) A10K2.u767 from rfl, totK_node, atot766, atot767]
  decide +kernel

theorem arows771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u771 = true := by
  rw [show A10K2.u771 = KTree.node A10K2.u769 (nat_lit 12877831) (nat_lit 13733820557) (nat_lit 0) A10K2.u770 from rfl, allE_node, arows769, irow771, arows770]
  all_goals rfl

theorem atot771 : totK PA10K2 A10K2.u771 = [0, 207752958981, 2661319658205, 7418327502212, 7133641945188, 2053347339819, 143543549817, 0, 0, 0] := by
  rw [show A10K2.u771 = KTree.node A10K2.u769 (nat_lit 12877831) (nat_lit 13733820557) (nat_lit 0) A10K2.u770 from rfl, totK_node, atot769, atot770]
  decide +kernel

theorem arows775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u775 = true := by
  rw [show A10K2.u775 = KTree.node A10K2.u773 (nat_lit 12896552) (nat_lit 12023766111) (nat_lit 0) A10K2.u774 from rfl, allE_node, arows773, irow775, arows774]
  all_goals rfl

theorem atot775 : totK PA10K2 A10K2.u775 = [0, 0, 1309998776816, 5349228994692, 7489701012120, 3837438569199, 709778993727, 36134558889, 0, 0] := by
  rw [show A10K2.u775 = KTree.node A10K2.u773 (nat_lit 12896552) (nat_lit 12023766111) (nat_lit 0) A10K2.u774 from rfl, totK_node, atot773, atot774]
  decide +kernel

theorem arows778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u778 = true := by
  rw [show A10K2.u778 = KTree.node A10K2.u776 (nat_lit 12980216) (nat_lit 12700097607) (nat_lit 0) A10K2.u777 from rfl, allE_node, arows776, irow778, arows777]
  all_goals rfl

theorem atot778 : totK PA10K2 A10K2.u778 = [0, 1188245396710, 5051265001302, 7724429825073, 4638443757149, 973604862914, 59842360860, 0, 0, 0] := by
  rw [show A10K2.u778 = KTree.node A10K2.u776 (nat_lit 12980216) (nat_lit 12700097607) (nat_lit 0) A10K2.u777 from rfl, totK_node, atot776, atot777]
  decide +kernel

theorem arows783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u783 = true := by
  rw [show A10K2.u783 = KTree.node A10K2.u781 (nat_lit 13009164) (nat_lit 11886457402) (nat_lit 0) A10K2.u782 from rfl, allE_node, arows781, irow783, arows782]
  all_goals rfl

theorem atot783 : totK PA10K2 A10K2.u783 = [0, 345735655366, 3326532206651, 7851853752167, 6121030798695, 1330329333730, 69639688133, 0, 0, 0] := by
  rw [show A10K2.u783 = KTree.node A10K2.u781 (nat_lit 13009164) (nat_lit 11886457402) (nat_lit 0) A10K2.u782 from rfl, totK_node, atot781, atot782]
  decide +kernel

theorem arows786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u786 = true := by
  rw [show A10K2.u786 = KTree.node A10K2.u784 (nat_lit 13042134) (nat_lit 15094163299) (nat_lit 0) A10K2.u785 from rfl, allE_node, arows784, irow786, arows785]
  all_goals rfl

theorem atot786 : totK PA10K2 A10K2.u786 = [0, 801349738877, 3697044557824, 6709240859669, 5709725931544, 1972830387043, 223507073729, 5676195732, 0, 0] := by
  rw [show A10K2.u786 = KTree.node A10K2.u784 (nat_lit 13042134) (nat_lit 15094163299) (nat_lit 0) A10K2.u785 from rfl, totK_node, atot784, atot785]
  decide +kernel

theorem arows790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u790 = true := by
  rw [show A10K2.u790 = KTree.node A10K2.u788 (nat_lit 13055714) (nat_lit 13644254986) (nat_lit 0) A10K2.u789 from rfl, allE_node, arows788, irow790, arows789]
  all_goals rfl

theorem atot790 : totK PA10K2 A10K2.u790 = [0, 1420410377238, 6049465393694, 8262348195947, 3767704416970, 439569375606, 7151180950, 0, 0, 0] := by
  rw [show A10K2.u790 = KTree.node A10K2.u788 (nat_lit 13055714) (nat_lit 13644254986) (nat_lit 0) A10K2.u789 from rfl, totK_node, atot788, atot789]
  decide +kernel

theorem arows793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u793 = true := by
  rw [show A10K2.u793 = KTree.node A10K2.u791 (nat_lit 13182217) (nat_lit 3192150019) (nat_lit 0) A10K2.u792 from rfl, allE_node, arows791, irow793, arows792]
  all_goals rfl

theorem atot793 : totK PA10K2 A10K2.u793 = [847358390021, 3425012474075, 5321905922591, 5359125944457, 3826331049904, 1016462754236, 62368562949, 0, 0, 0] := by
  rw [show A10K2.u793 = KTree.node A10K2.u791 (nat_lit 13182217) (nat_lit 3192150019) (nat_lit 0) A10K2.u792 from rfl, totK_node, atot791, atot792]
  decide +kernel

theorem arows799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u799 = true := by
  rw [show A10K2.u799 = KTree.node A10K2.u797 (nat_lit 13191937) (nat_lit 9272234030) (nat_lit 0) A10K2.u798 from rfl, allE_node, arows797, irow799, arows798]
  all_goals rfl

theorem atot799 : totK PA10K2 A10K2.u799 = [1201130396958, 5263189543735, 7805203863663, 4382873209827, 821371650282, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u799 = KTree.node A10K2.u797 (nat_lit 13191937) (nat_lit 9272234030) (nat_lit 0) A10K2.u798 from rfl, totK_node, atot797, atot798]
  decide +kernel

theorem arows802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u802 = true := by
  rw [show A10K2.u802 = KTree.node A10K2.u800 (nat_lit 13205395) (nat_lit 9696916977) (nat_lit 0) A10K2.u801 from rfl, allE_node, arows800, irow802, arows801]
  all_goals rfl

theorem atot802 : totK PA10K2 A10K2.u802 = [162737985116, 2460118119919, 7436331581983, 7476766681472, 2270373516553, 151257374557, 0, 0, 0, 0] := by
  rw [show A10K2.u802 = KTree.node A10K2.u800 (nat_lit 13205395) (nat_lit 9696916977) (nat_lit 0) A10K2.u801 from rfl, totK_node, atot800, atot801]
  decide +kernel

theorem arows806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u806 = true := by
  rw [show A10K2.u806 = KTree.node A10K2.u804 (nat_lit 13224222) (nat_lit 9207398433) (nat_lit 0) A10K2.u805 from rfl, allE_node, arows804, irow806, arows805]
  all_goals rfl

theorem atot806 : totK PA10K2 A10K2.u806 = [0, 1047849526647, 5012824576788, 7932869005040, 4439650376680, 783211984482, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u806 = KTree.node A10K2.u804 (nat_lit 13224222) (nat_lit 9207398433) (nat_lit 0) A10K2.u805 from rfl, totK_node, atot804, atot805]
  decide +kernel

theorem arows809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u809 = true := by
  rw [show A10K2.u809 = KTree.node A10K2.u807 (nat_lit 13307963) (nat_lit 4182520775) (nat_lit 0) A10K2.u808 from rfl, allE_node, arows807, irow809, arows808]
  all_goals rfl

theorem atot809 : totK PA10K2 A10K2.u809 = [1334277149280, 5456158937258, 7699725173303, 4484787316115, 1064014218952, 75719345802, 0, 0, 0, 0] := by
  rw [show A10K2.u809 = KTree.node A10K2.u807 (nat_lit 13307963) (nat_lit 4182520775) (nat_lit 0) A10K2.u808 from rfl, totK_node, atot807, atot808]
  decide +kernel

theorem arows814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u814 = true := by
  rw [show A10K2.u814 = KTree.node A10K2.u812 (nat_lit 13328930) (nat_lit 11933677) (nat_lit 0) A10K2.u813 from rfl, allE_node, arows812, irow814, arows813]
  all_goals rfl

theorem atot814 : totK PA10K2 A10K2.u814 = [912224543933, 4810917202725, 8220858459502, 5026800857570, 924248260820, 38600540508, 0, 0, 0, 0] := by
  rw [show A10K2.u814 = KTree.node A10K2.u812 (nat_lit 13328930) (nat_lit 11933677) (nat_lit 0) A10K2.u813 from rfl, totK_node, atot812, atot813]
  decide +kernel

theorem arows817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u817 = true := by
  rw [show A10K2.u817 = KTree.node A10K2.u815 (nat_lit 13340095) (nat_lit 14297797703) (nat_lit 0) A10K2.u816 from rfl, allE_node, arows815, irow817, arows816]
  all_goals rfl

theorem atot817 : totK PA10K2 A10K2.u817 = [0, 1605676604716, 6357732525518, 8140308734075, 3558764394659, 431828155518, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u817 = KTree.node A10K2.u815 (nat_lit 13340095) (nat_lit 14297797703) (nat_lit 0) A10K2.u816 from rfl, totK_node, atot815, atot816]
  decide +kernel

theorem arows821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u821 = true := by
  rw [show A10K2.u821 = KTree.node A10K2.u819 (nat_lit 13361422) (nat_lit 11211425880) (nat_lit 0) A10K2.u820 from rfl, allE_node, arows819, irow821, arows820]
  all_goals rfl

theorem atot821 : totK PA10K2 A10K2.u821 = [0, 1171031756239, 5616770092950, 8357360612787, 4197568045457, 544420700771, 13113983930, 0, 0, 0] := by
  rw [show A10K2.u821 = KTree.node A10K2.u819 (nat_lit 13361422) (nat_lit 11211425880) (nat_lit 0) A10K2.u820 from rfl, totK_node, atot819, atot820]
  decide +kernel

theorem arows824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u824 = true := by
  rw [show A10K2.u824 = KTree.node A10K2.u822 (nat_lit 13445288) (nat_lit 7938923147) (nat_lit 0) A10K2.u823 from rfl, allE_node, arows822, irow824, arows823]
  all_goals rfl

theorem atot824 : totK PA10K2 A10K2.u824 = [0, 846871377146, 4262261329932, 7629647891659, 5467711362839, 1272625863255, 80777700920, 0, 0, 0] := by
  rw [show A10K2.u824 = KTree.node A10K2.u822 (nat_lit 13445288) (nat_lit 7938923147) (nat_lit 0) A10K2.u823 from rfl, totK_node, atot822, atot823]
  decide +kernel

theorem arows831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u831 = true := by
  rw [show A10K2.u831 = KTree.node A10K2.u829 (nat_lit 13457645) (nat_lit 5975387072) (nat_lit 0) A10K2.u830 from rfl, allE_node, arows829, irow831, arows830]
  all_goals rfl

theorem atot831 : totK PA10K2 A10K2.u831 = [0, 1362400161870, 5919563265333, 8206034876567, 3759538413496, 471638324996, 12273889295, 0, 0, 0] := by
  rw [show A10K2.u831 = KTree.node A10K2.u829 (nat_lit 13457645) (nat_lit 5975387072) (nat_lit 0) A10K2.u830 from rfl, totK_node, atot829, atot830]
  decide +kernel

theorem arows834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u834 = true := by
  rw [show A10K2.u834 = KTree.node A10K2.u832 (nat_lit 13477760) (nat_lit 6554190571) (nat_lit 0) A10K2.u833 from rfl, allE_node, arows832, irow834, arows833]
  all_goals rfl

theorem atot834 : totK PA10K2 A10K2.u834 = [0, 0, 1552719346868, 6288862906485, 7821116873427, 3254800176470, 492290288971, 25565504801, 0, 0] := by
  rw [show A10K2.u834 = KTree.node A10K2.u832 (nat_lit 13477760) (nat_lit 6554190571) (nat_lit 0) A10K2.u833 from rfl, totK_node, atot832, atot833]
  decide +kernel

theorem arows838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u838 = true := by
  rw [show A10K2.u838 = KTree.node A10K2.u836 (nat_lit 13490444) (nat_lit 12110809241) (nat_lit 0) A10K2.u837 from rfl, allE_node, arows836, irow838, arows837]
  all_goals rfl

theorem atot838 : totK PA10K2 A10K2.u838 = [0, 285766734819, 2224199185990, 6182111318872, 7203098738477, 3116187720282, 408586237677, 11138589073, 0, 0] := by
  rw [show A10K2.u838 = KTree.node A10K2.u836 (nat_lit 13490444) (nat_lit 12110809241) (nat_lit 0) A10K2.u837 from rfl, totK_node, atot836, atot837]
  decide +kernel

theorem arows841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u841 = true := by
  rw [show A10K2.u841 = KTree.node A10K2.u839 (nat_lit 13575840) (nat_lit 5148787316) (nat_lit 0) A10K2.u840 from rfl, allE_node, arows839, irow841, arows840]
  all_goals rfl

theorem atot841 : totK PA10K2 A10K2.u841 = [0, 1093297246801, 5257714444367, 8223763770179, 4608028875884, 786623022046, 32668625165, 0, 0, 0] := by
  rw [show A10K2.u841 = KTree.node A10K2.u839 (nat_lit 13575840) (nat_lit 5148787316) (nat_lit 0) A10K2.u840 from rfl, totK_node, atot839, atot840]
  decide +kernel

theorem arows846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u846 = true := by
  rw [show A10K2.u846 = KTree.node A10K2.u844 (nat_lit 13594174) (nat_lit 16016731137) (nat_lit 0) A10K2.u845 from rfl, allE_node, arows844, irow846, arows845]
  all_goals rfl

theorem atot846 : totK PA10K2 A10K2.u846 = [76628528242, 953711619165, 4368550787799, 7801365134680, 5518267835849, 1241343052928, 68006876977, 0, 0, 0] := by
  rw [show A10K2.u846 = KTree.node A10K2.u844 (nat_lit 13594174) (nat_lit 16016731137) (nat_lit 0) A10K2.u845 from rfl, totK_node, atot844, atot845]
  decide +kernel

theorem arows849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u849 = true := by
  rw [show A10K2.u849 = KTree.node A10K2.u847 (nat_lit 14160388) (nat_lit 11725904797) (nat_lit 0) A10K2.u848 from rfl, allE_node, arows847, irow849, arows848]
  all_goals rfl

theorem atot849 : totK PA10K2 A10K2.u849 = [1221757699254, 5552014314954, 7905455783479, 3994370211912, 668351588746, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u849 = KTree.node A10K2.u847 (nat_lit 14160388) (nat_lit 11725904797) (nat_lit 0) A10K2.u848 from rfl, totK_node, atot847, atot848]
  decide +kernel

theorem arows853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u853 = true := by
  rw [show A10K2.u853 = KTree.node A10K2.u851 (nat_lit 14183972) (nat_lit 8510104515) (nat_lit 0) A10K2.u852 from rfl, allE_node, arows851, irow853, arows852]
  all_goals rfl

theorem atot853 : totK PA10K2 A10K2.u853 = [828922211760, 4357793732550, 7975715150420, 5590428565212, 1291229209787, 69334249866, 0, 0, 0, 0] := by
  rw [show A10K2.u853 = KTree.node A10K2.u851 (nat_lit 14183972) (nat_lit 8510104515) (nat_lit 0) A10K2.u852 from rfl, totK_node, atot851, atot852]
  decide +kernel

theorem arows856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u856 = true := by
  rw [show A10K2.u856 = KTree.node A10K2.u854 (nat_lit 14193248) (nat_lit 13505485590) (nat_lit 0) A10K2.u855 from rfl, allE_node, arows854, irow856, arows855]
  all_goals rfl

theorem atot856 : totK PA10K2 A10K2.u856 = [0, 1178593474843, 5508687635224, 7927767025919, 3807850510894, 631776047159, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u856 = KTree.node A10K2.u854 (nat_lit 14193248) (nat_lit 13505485590) (nat_lit 0) A10K2.u855 from rfl, totK_node, atot854, atot855]
  decide +kernel

theorem arows862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u862 = true := by
  rw [show A10K2.u862 = KTree.node A10K2.u860 (nat_lit 14217111) (nat_lit 14574469560) (nat_lit 0) A10K2.u861 from rfl, allE_node, arows860, irow862, arows861]
  all_goals rfl

theorem atot862 : totK PA10K2 A10K2.u862 = [781136855443, 3999625163697, 7210603100843, 5710578399571, 1961953837774, 231368754759, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u862 = KTree.node A10K2.u860 (nat_lit 14217111) (nat_lit 14574469560) (nat_lit 0) A10K2.u861 from rfl, totK_node, atot860, atot861]
  decide +kernel

theorem arows865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u865 = true := by
  rw [show A10K2.u865 = KTree.node A10K2.u863 (nat_lit 14246342) (nat_lit 15671917983) (nat_lit 0) A10K2.u864 from rfl, allE_node, arows863, irow865, arows864]
  all_goals rfl

theorem atot865 : totK PA10K2 A10K2.u865 = [1095156759403, 5098086607361, 8110978853812, 4898406447880, 918599804022, 38620453579, 0, 0, 0, 0] := by
  rw [show A10K2.u865 = KTree.node A10K2.u863 (nat_lit 14246342) (nat_lit 15671917983) (nat_lit 0) A10K2.u864 from rfl, totK_node, atot863, atot864]
  decide +kernel

theorem arows869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u869 = true := by
  rw [show A10K2.u869 = KTree.node A10K2.u867 (nat_lit 14265014) (nat_lit 15076288878) (nat_lit 0) A10K2.u868 from rfl, allE_node, arows867, irow869, arows868]
  all_goals rfl

theorem atot869 : totK PA10K2 A10K2.u869 = [0, 1386059391295, 5844247429518, 7933283880662, 3835681988413, 634502075028, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u869 = KTree.node A10K2.u867 (nat_lit 14265014) (nat_lit 15076288878) (nat_lit 0) A10K2.u868 from rfl, totK_node, atot867, atot868]
  decide +kernel

theorem arows872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u872 = true := by
  rw [show A10K2.u872 = KTree.node A10K2.u870 (nat_lit 14282166) (nat_lit 17179869184) (nat_lit 0) A10K2.u871 from rfl, allE_node, arows870, irow872, arows871]
  all_goals rfl

theorem atot872 : totK PA10K2 A10K2.u872 = [766127300133, 3789707798253, 7171633992427, 6133762295030, 1938270116763, 142899785518, 0, 0, 0, 0] := by
  rw [show A10K2.u872 = KTree.node A10K2.u870 (nat_lit 14282166) (nat_lit 17179869184) (nat_lit 0) A10K2.u871 from rfl, totK_node, atot870, atot871]
  decide +kernel

theorem arows877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u877 = true := by
  rw [show A10K2.u877 = KTree.node A10K2.u875 (nat_lit 14363282) (nat_lit 15529038244) (nat_lit 0) A10K2.u876 from rfl, allE_node, arows875, irow877, arows876]
  all_goals rfl

theorem atot877 : totK PA10K2 A10K2.u877 = [838649238306, 4342178031781, 7843552721888, 5222697733627, 1048943039766, 55499621093, 0, 0, 0, 0] := by
  rw [show A10K2.u877 = KTree.node A10K2.u875 (nat_lit 14363282) (nat_lit 15529038244) (nat_lit 0) A10K2.u876 from rfl, totK_node, atot875, atot876]
  decide +kernel

theorem arows880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u880 = true := by
  rw [show A10K2.u880 = KTree.node A10K2.u878 (nat_lit 14381458) (nat_lit 14077518487) (nat_lit 0) A10K2.u879 from rfl, allE_node, arows878, irow880, arows879]
  all_goals rfl

theorem atot880 : totK PA10K2 A10K2.u880 = [784061127931, 4287590478434, 7861275845185, 5569671981864, 1341952205611, 83117535345, 0, 0, 0, 0] := by
  rw [show A10K2.u880 = KTree.node A10K2.u878 (nat_lit 14381458) (nat_lit 14077518487) (nat_lit 0) A10K2.u879 from rfl, totK_node, atot878, atot879]
  decide +kernel

theorem arows884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u884 = true := by
  rw [show A10K2.u884 = KTree.node A10K2.u882 (nat_lit 14392704) (nat_lit 15104162539) (nat_lit 0) A10K2.u883 from rfl, allE_node, arows882, irow884, arows883]
  all_goals rfl

theorem atot884 : totK PA10K2 A10K2.u884 = [0, 1196775515639, 5586495946240, 8263180957178, 3976155286886, 475649996706, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u884 = KTree.node A10K2.u882 (nat_lit 14392704) (nat_lit 15104162539) (nat_lit 0) A10K2.u883 from rfl, totK_node, atot882, atot883]
  decide +kernel

theorem arows887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u887 = true := by
  rw [show A10K2.u887 = KTree.node A10K2.u885 (nat_lit 14413207) (nat_lit 14616934806) (nat_lit 0) A10K2.u886 from rfl, allE_node, arows885, irow887, arows886]
  all_goals rfl

theorem atot887 : totK PA10K2 A10K2.u887 = [0, 892005830457, 4586182048196, 7999280185218, 5283240556551, 986831223289, 30846741173, 0, 0, 0] := by
  rw [show A10K2.u887 = KTree.node A10K2.u885 (nat_lit 14413207) (nat_lit 14616934806) (nat_lit 0) A10K2.u886 from rfl, totK_node, atot885, atot886]
  decide +kernel

theorem arows895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u895 = true := by
  rw [show A10K2.u895 = KTree.node A10K2.u893 (nat_lit 14422336) (nat_lit 14880619127) (nat_lit 0) A10K2.u894 from rfl, allE_node, arows893, irow895, arows894]
  all_goals rfl

theorem atot895 : totK PA10K2 A10K2.u895 = [0, 1297886853924, 5450084272399, 7581240923774, 4106926122877, 885692106717, 68090850563, 0, 0, 0] := by
  rw [show A10K2.u895 = KTree.node A10K2.u893 (nat_lit 14422336) (nat_lit 14880619127) (nat_lit 0) A10K2.u894 from rfl, totK_node, atot893, atot894]
  decide +kernel

theorem arows898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u898 = true := by
  rw [show A10K2.u898 = KTree.node A10K2.u896 (nat_lit 14445970) (nat_lit 14729699888) (nat_lit 0) A10K2.u897 from rfl, allE_node, arows896, irow898, arows897]
  all_goals rfl

theorem atot898 : totK PA10K2 A10K2.u898 = [0, 827418959121, 4438401499607, 8144402700997, 5533323996829, 1074617562704, 30742029818, 0, 0, 0] := by
  rw [show A10K2.u898 = KTree.node A10K2.u896 (nat_lit 14445970) (nat_lit 14729699888) (nat_lit 0) A10K2.u897 from rfl, totK_node, atot896, atot897]
  decide +kernel

theorem arows902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u902 = true := by
  rw [show A10K2.u902 = KTree.node A10K2.u900 (nat_lit 14455241) (nat_lit 6837354806) (nat_lit 0) A10K2.u901 from rfl, allE_node, arows900, irow902, arows901]
  all_goals rfl

theorem atot902 : totK PA10K2 A10K2.u902 = [0, 0, 1584873598385, 6386044537178, 7820342459217, 3100394564302, 377149992746, 7007974415, 0, 0] := by
  rw [show A10K2.u902 = KTree.node A10K2.u900 (nat_lit 14455241) (nat_lit 6837354806) (nat_lit 0) A10K2.u901 from rfl, totK_node, atot900, atot901]
  decide +kernel

theorem arows905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u905 = true := by
  rw [show A10K2.u905 = KTree.node A10K2.u903 (nat_lit 14493980) (nat_lit 12193009390) (nat_lit 0) A10K2.u904 from rfl, allE_node, arows903, irow905, arows904]
  all_goals rfl

theorem atot905 : totK PA10K2 A10K2.u905 = [0, 780638625629, 4133153214163, 7647134736520, 5757102296254, 1507846973839, 100096519661, 0, 0, 0] := by
  rw [show A10K2.u905 = KTree.node A10K2.u903 (nat_lit 14493980) (nat_lit 12193009390) (nat_lit 0) A10K2.u904 from rfl, totK_node, atot903, atot904]
  decide +kernel

theorem arows910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u910 = true := by
  rw [show A10K2.u910 = KTree.node A10K2.u908 (nat_lit 14511177) (nat_lit 9179824636) (nat_lit 0) A10K2.u909 from rfl, allE_node, arows908, irow910, arows909]
  all_goals rfl

theorem atot910 : totK PA10K2 A10K2.u910 = [0, 1093657370475, 5155291826486, 8262479368581, 4884271182453, 817612274315, 19087212590, 0, 0, 0] := by
  rw [show A10K2.u910 = KTree.node A10K2.u908 (nat_lit 14511177) (nat_lit 9179824636) (nat_lit 0) A10K2.u909 from rfl, totK_node, atot908, atot909]
  decide +kernel

theorem arows913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u913 = true := by
  rw [show A10K2.u913 = KTree.node A10K2.u911 (nat_lit 14529879) (nat_lit 6097610107) (nat_lit 0) A10K2.u912 from rfl, allE_node, arows911, irow913, arows912]
  all_goals rfl

theorem atot913 : totK PA10K2 A10K2.u913 = [0, 0, 1548485713998, 6282551786379, 8106554514556, 3412303950234, 397461957124, 7151180950, 0, 0] := by
  rw [show A10K2.u913 = KTree.node A10K2.u911 (nat_lit 14529879) (nat_lit 6097610107) (nat_lit 0) A10K2.u912 from rfl, totK_node, atot911, atot912]
  decide +kernel

theorem arows917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u917 = true := by
  rw [show A10K2.u917 = KTree.node A10K2.u915 (nat_lit 14618166) (nat_lit 16393281810) (nat_lit 0) A10K2.u916 from rfl, allE_node, arows915, irow917, arows916]
  all_goals rfl

theorem atot917 : totK PA10K2 A10K2.u917 = [0, 1056872926040, 4843708101704, 7690019621991, 4878875812790, 1104587018309, 62423992767, 0, 0, 0] := by
  rw [show A10K2.u917 = KTree.node A10K2.u915 (nat_lit 14618166) (nat_lit 16393281810) (nat_lit 0) A10K2.u916 from rfl, totK_node, atot915, atot916]
  decide +kernel

theorem arows920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u920 = true := by
  rw [show A10K2.u920 = KTree.node A10K2.u918 (nat_lit 14630281) (nat_lit 8068193115) (nat_lit 0) A10K2.u919 from rfl, allE_node, arows918, irow920, arows919]
  all_goals rfl

theorem atot920 : totK PA10K2 A10K2.u920 = [0, 1328979995628, 5791632672225, 8127714863737, 3995161412922, 550537170072, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u920 = KTree.node A10K2.u918 (nat_lit 14630281) (nat_lit 8068193115) (nat_lit 0) A10K2.u919 from rfl, totK_node, atot918, atot919]
  decide +kernel

theorem arows926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u926 = true := by
  rw [show A10K2.u926 = KTree.node A10K2.u924 (nat_lit 14647800) (nat_lit 13324120295) (nat_lit 0) A10K2.u925 from rfl, allE_node, arows924, irow926, arows925]
  all_goals rfl

theorem atot926 : totK PA10K2 A10K2.u926 = [0, 0, 1582334102280, 6488536232260, 8216816235946, 3151840364937, 308724417732, 6318667960, 0, 0] := by
  rw [show A10K2.u926 = KTree.node A10K2.u924 (nat_lit 14647800) (nat_lit 13324120295) (nat_lit 0) A10K2.u925 from rfl, totK_node, atot924, atot925]
  decide +kernel

theorem arows929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u929 = true := by
  rw [show A10K2.u929 = KTree.node A10K2.u927 (nat_lit 14661346) (nat_lit 13531178233) (nat_lit 0) A10K2.u928 from rfl, allE_node, arows927, irow929, arows928]
  all_goals rfl

theorem atot929 : totK PA10K2 A10K2.u929 = [0, 0, 1609856130838, 6440526871621, 7961734165010, 3287196930268, 350239129249, 6439430839, 0, 0] := by
  rw [show A10K2.u929 = KTree.node A10K2.u927 (nat_lit 14661346) (nat_lit 13531178233) (nat_lit 0) A10K2.u928 from rfl, totK_node, atot927, atot928]
  decide +kernel

theorem arows933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u933 = true := by
  rw [show A10K2.u933 = KTree.node A10K2.u931 (nat_lit 14680106) (nat_lit 6901439469) (nat_lit 0) A10K2.u932 from rfl, allE_node, arows931, irow933, arows932]
  all_goals rfl

theorem atot933 : totK PA10K2 A10K2.u933 = [0, 859381108411, 3456533549160, 5224784850432, 5222087304665, 3762635543295, 961189328672, 61018386929, 0, 0] := by
  rw [show A10K2.u933 = KTree.node A10K2.u931 (nat_lit 14680106) (nat_lit 6901439469) (nat_lit 0) A10K2.u932 from rfl, totK_node, atot931, atot932]
  decide +kernel

theorem arows936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u936 = true := by
  rw [show A10K2.u936 = KTree.node A10K2.u934 (nat_lit 14698605) (nat_lit 5512705346) (nat_lit 0) A10K2.u935 from rfl, allE_node, arows934, irow936, arows935]
  all_goals rfl

theorem atot936 : totK PA10K2 A10K2.u936 = [0, 1083055166203, 4900705129805, 7785897060654, 4520458554108, 786730432449, 36808095696, 0, 0, 0] := by
  rw [show A10K2.u936 = KTree.node A10K2.u934 (nat_lit 14698605) (nat_lit 5512705346) (nat_lit 0) A10K2.u935 from rfl, totK_node, atot934, atot935]
  decide +kernel

theorem arows941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u941 = true := by
  rw [show A10K2.u941 = KTree.node A10K2.u939 (nat_lit 14712027) (nat_lit 8288585007) (nat_lit 0) A10K2.u940 from rfl, allE_node, arows939, irow941, arows940]
  all_goals rfl

theorem atot941 : totK PA10K2 A10K2.u941 = [0, 357966842975, 3200690190064, 7839671223868, 6723183290422, 1679542330006, 93866176554, 0, 0, 0] := by
  rw [show A10K2.u941 = KTree.node A10K2.u939 (nat_lit 14712027) (nat_lit 8288585007) (nat_lit 0) A10K2.u940 from rfl, totK_node, atot939, atot940]
  decide +kernel

theorem arows944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u944 = true := by
  rw [show A10K2.u944 = KTree.node A10K2.u942 (nat_lit 14729992) (nat_lit 13865340433) (nat_lit 0) A10K2.u943 from rfl, allE_node, arows942, irow944, arows943]
  all_goals rfl

theorem atot944 : totK PA10K2 A10K2.u944 = [0, 0, 935896244343, 4758535582661, 7834055993444, 4401168448143, 778369758830, 36196801203, 0, 0] := by
  rw [show A10K2.u944 = KTree.node A10K2.u942 (nat_lit 14729992) (nat_lit 13865340433) (nat_lit 0) A10K2.u943 from rfl, totK_node, atot942, atot943]
  decide +kernel

theorem arows948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u948 = true := by
  rw [show A10K2.u948 = KTree.node A10K2.u946 (nat_lit 14813330) (nat_lit 9531677408) (nat_lit 0) A10K2.u947 from rfl, allE_node, arows946, irow948, arows947]
  all_goals rfl

theorem atot948 : totK PA10K2 A10K2.u948 = [0, 793832741517, 4063568351798, 7479661309702, 5750802604049, 1557132529441, 108129570852, 0, 0, 0] := by
  rw [show A10K2.u948 = KTree.node A10K2.u946 (nat_lit 14813330) (nat_lit 9531677408) (nat_lit 0) A10K2.u947 from rfl, totK_node, atot946, atot947]
  decide +kernel

theorem arows951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u951 = true := by
  rw [show A10K2.u951 = KTree.node A10K2.u949 (nat_lit 14832800) (nat_lit 7645135455) (nat_lit 0) A10K2.u950 from rfl, allE_node, arows949, irow951, arows950]
  all_goals rfl

theorem atot951 : totK PA10K2 A10K2.u951 = [0, 741023122864, 4326638032316, 8097582271628, 5101038992378, 905339133412, 37964298760, 0, 0, 0] := by
  rw [show A10K2.u951 = KTree.node A10K2.u949 (nat_lit 14832800) (nat_lit 7645135455) (nat_lit 0) A10K2.u950 from rfl, totK_node, atot949, atot950]
  decide +kernel

theorem arows958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u958 = true := by
  rw [show A10K2.u958 = KTree.node A10K2.u956 (nat_lit 14865699) (nat_lit 10289999058) (nat_lit 0) A10K2.u957 from rfl, allE_node, arows956, irow958, arows957]
  all_goals rfl

theorem atot958 : totK PA10K2 A10K2.u958 = [0, 801349738877, 3548188897067, 6487333814080, 6019187207766, 2106332515066, 230967586798, 5976421810, 0, 0] := by
  rw [show A10K2.u958 = KTree.node A10K2.u956 (nat_lit 14865699) (nat_lit 10289999058) (nat_lit 0) A10K2.u957 from rfl, totK_node, atot956, atot957]
  decide +kernel

theorem arows961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u961 = true := by
  rw [show A10K2.u961 = KTree.node A10K2.u959 (nat_lit 14887991) (nat_lit 14928820787) (nat_lit 0) A10K2.u960 from rfl, allE_node, arows959, irow961, arows960]
  all_goals rfl

theorem atot961 : totK PA10K2 A10K2.u961 = [0, 844667634583, 4567028967432, 8188927024918, 5219956688680, 994241908969, 43492424891, 0, 0, 0] := by
  rw [show A10K2.u961 = KTree.node A10K2.u959 (nat_lit 14887991) (nat_lit 14928820787) (nat_lit 0) A10K2.u960 from rfl, totK_node, atot959, atot960]
  decide +kernel

theorem arows965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u965 = true := by
  rw [show A10K2.u965 = KTree.node A10K2.u963 (nat_lit 14906823) (nat_lit 14357336368) (nat_lit 0) A10K2.u964 from rfl, allE_node, arows963, irow965, arows964]
  all_goals rfl

theorem atot965 : totK PA10K2 A10K2.u965 = [0, 576020245237, 3601565471955, 7677964502081, 6244713317561, 1592505150873, 94077257328, 0, 0, 0] := by
  rw [show A10K2.u965 = KTree.node A10K2.u963 (nat_lit 14906823) (nat_lit 14357336368) (nat_lit 0) A10K2.u964 from rfl, totK_node, atot963, atot964]
  decide +kernel

theorem arows968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u968 = true := by
  rw [show A10K2.u968 = KTree.node A10K2.u966 (nat_lit 14919386) (nat_lit 13978935762) (nat_lit 0) A10K2.u967 from rfl, allE_node, arows966, irow968, arows967]
  all_goals rfl

theorem atot968 : totK PA10K2 A10K2.u968 = [0, 0, 1039643357424, 5153604885107, 8363414763088, 4698565312026, 641025267107, 13671283666, 0, 0] := by
  rw [show A10K2.u968 = KTree.node A10K2.u966 (nat_lit 14919386) (nat_lit 13978935762) (nat_lit 0) A10K2.u967 from rfl, totK_node, atot966, atot967]
  decide +kernel

theorem arows973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u973 = true := by
  rw [show A10K2.u973 = KTree.node A10K2.u971 (nat_lit 14939419) (nat_lit 9324785834) (nat_lit 0) A10K2.u972 from rfl, allE_node, arows971, irow973, arows972]
  all_goals rfl

theorem atot973 : totK PA10K2 A10K2.u973 = [0, 0, 1142576948704, 5057031609039, 7647247609005, 4646687788672, 1004488158019, 61110126106, 0, 0] := by
  rw [show A10K2.u973 = KTree.node A10K2.u971 (nat_lit 14939419) (nat_lit 9324785834) (nat_lit 0) A10K2.u972 from rfl, totK_node, atot971, atot972]
  decide +kernel

theorem arows976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u976 = true := by
  rw [show A10K2.u976 = KTree.node A10K2.u974 (nat_lit 14949566) (nat_lit 15874411725) (nat_lit 0) A10K2.u975 from rfl, allE_node, arows974, irow976, arows975]
  all_goals rfl

theorem atot976 : totK PA10K2 A10K2.u976 = [0, 0, 933895640380, 4915385586480, 8139744589479, 4352096377364, 685541288937, 30831673886, 0, 0] := by
  rw [show A10K2.u976 = KTree.node A10K2.u974 (nat_lit 14949566) (nat_lit 15874411725) (nat_lit 0) A10K2.u975 from rfl, totK_node, atot974, atot975]
  decide +kernel

theorem arows980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u980 = true := by
  rw [show A10K2.u980 = KTree.node A10K2.u978 (nat_lit 14970930) (nat_lit 10202622730) (nat_lit 0) A10K2.u979 from rfl, allE_node, arows978, irow980, arows979]
  all_goals rfl

theorem atot980 : totK PA10K2 A10K2.u980 = [0, 0, 799225256197, 4252844334561, 7874655947873, 5566767150351, 1228098996951, 66403269668, 0, 0] := by
  rw [show A10K2.u980 = KTree.node A10K2.u978 (nat_lit 14970930) (nat_lit 10202622730) (nat_lit 0) A10K2.u979 from rfl, totK_node, atot978, atot979]
  decide +kernel

theorem arows983 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u983 = true := by
  rw [show A10K2.u983 = KTree.node A10K2.u981 (nat_lit 14982655) (nat_lit 9967620085) (nat_lit 0) A10K2.u982 from rfl, allE_node, arows981, irow983, arows982]
  all_goals rfl

theorem atot983 : totK PA10K2 A10K2.u983 = [0, 0, 0, 1704987031918, 6554062793063, 7646226247929, 2791302253234, 339360155128, 7237400819, 0] := by
  rw [show A10K2.u983 = KTree.node A10K2.u981 (nat_lit 14982655) (nat_lit 9967620085) (nat_lit 0) A10K2.u982 from rfl, totK_node, atot981, atot982]
  decide +kernel

theorem arows989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u989 = true := by
  rw [show A10K2.u989 = KTree.node A10K2.u987 (nat_lit 15077367) (nat_lit 14849519599) (nat_lit 0) A10K2.u988 from rfl, allE_node, arows987, irow989, arows988]
  all_goals rfl

theorem atot989 : totK PA10K2 A10K2.u989 = [0, 0, 1344134215454, 5698226490085, 7952238566274, 3785437665575, 625212899967, 34471179867, 0, 0] := by
  rw [show A10K2.u989 = KTree.node A10K2.u987 (nat_lit 15077367) (nat_lit 14849519599) (nat_lit 0) A10K2.u988 from rfl, totK_node, atot987, atot988]
  decide +kernel

theorem arows992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u992 = true := by
  rw [show A10K2.u992 = KTree.node A10K2.u990 (nat_lit 15139693) (nat_lit 5387155054) (nat_lit 0) A10K2.u991 from rfl, allE_node, arows990, irow992, arows991]
  all_goals rfl

theorem atot992 : totK PA10K2 A10K2.u992 = [0, 0, 991196575499, 5143169427040, 8212778091691, 4222400930658, 622183663978, 18827489321, 0, 0] := by
  rw [show A10K2.u992 = KTree.node A10K2.u990 (nat_lit 15139693) (nat_lit 5387155054) (nat_lit 0) A10K2.u991 from rfl, totK_node, atot990, atot991]
  decide +kernel

theorem arows996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u996 = true := by
  rw [show A10K2.u996 = KTree.node A10K2.u994 (nat_lit 15154561) (nat_lit 8979806855) (nat_lit 0) A10K2.u995 from rfl, allE_node, arows994, irow996, arows995]
  all_goals rfl

theorem atot996 : totK PA10K2 A10K2.u996 = [0, 0, 1420410377238, 6007988924904, 8279227909383, 3822474556019, 419164977907, 6860445330, 0, 0] := by
  rw [show A10K2.u996 = KTree.node A10K2.u994 (nat_lit 15154561) (nat_lit 8979806855) (nat_lit 0) A10K2.u995 from rfl, totK_node, atot994, atot995]
  decide +kernel

theorem arows999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u999 = true := by
  rw [show A10K2.u999 = KTree.node A10K2.u997 (nat_lit 15279803) (nat_lit 7122795149) (nat_lit 0) A10K2.u998 from rfl, allE_node, arows997, irow999, arows998]
  all_goals rfl

theorem atot999 : totK PA10K2 A10K2.u999 = [0, 847358390021, 3497253351413, 5439128321007, 5237921589142, 3642223779677, 979397254089, 62368562949, 0, 0] := by
  rw [show A10K2.u999 = KTree.node A10K2.u997 (nat_lit 15279803) (nat_lit 7122795149) (nat_lit 0) A10K2.u998 from rfl, totK_node, atot997, atot998]
  decide +kernel

theorem arows1004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1004 = true := by
  rw [show A10K2.u1004 = KTree.node A10K2.u1002 (nat_lit 15291683) (nat_lit 10289999058) (nat_lit 0) A10K2.u1003 from rfl, allE_node, arows1002, irow1004, arows1003]
  all_goals rfl

theorem atot1004 : totK PA10K2 A10K2.u1004 = [0, 1363868382074, 5786502055192, 8069020657785, 3844906487821, 497098993032, 12016267967, 0, 0, 0] := by
  rw [show A10K2.u1004 = KTree.node A10K2.u1002 (nat_lit 15291683) (nat_lit 10289999058) (nat_lit 0) A10K2.u1003 from rfl, totK_node, atot1002, atot1003]
  decide +kernel

theorem arows1007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1007 = true := by
  rw [show A10K2.u1007 = KTree.node A10K2.u1005 (nat_lit 15312192) (nat_lit 3751336308) (nat_lit 0) A10K2.u1006 from rfl, allE_node, arows1005, irow1007, arows1006]
  all_goals rfl

theorem atot1007 : totK PA10K2 A10K2.u1007 = [0, 0, 1870756571324, 6955723687598, 7833816386618, 2801615804490, 343876534899, 20331139758, 0, 0] := by
  rw [show A10K2.u1007 = KTree.node A10K2.u1005 (nat_lit 15312192) (nat_lit 3751336308) (nat_lit 0) A10K2.u1006 from rfl, totK_node, atot1005, atot1006]
  decide +kernel

theorem arows1011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1011 = true := by
  rw [show A10K2.u1011 = KTree.node A10K2.u1009 (nat_lit 15324330) (nat_lit 12978655923) (nat_lit 0) A10K2.u1010 from rfl, allE_node, arows1009, irow1011, arows1010]
  all_goals rfl

theorem atot1011 : totK PA10K2 A10K2.u1011 = [0, 0, 1361874081439, 5663845224972, 7800736468734, 3851144431849, 575253393429, 16637449799, 0, 0] := by
  rw [show A10K2.u1011 = KTree.node A10K2.u1009 (nat_lit 15324330) (nat_lit 12978655923) (nat_lit 0) A10K2.u1010 from rfl, totK_node, atot1009, atot1010]
  decide +kernel

theorem arows1014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1014 = true := by
  rw [show A10K2.u1014 = KTree.node A10K2.u1012 (nat_lit 15405668) (nat_lit 10800171407) (nat_lit 0) A10K2.u1013 from rfl, allE_node, arows1012, irow1014, arows1013]
  all_goals rfl

theorem atot1014 : totK PA10K2 A10K2.u1014 = [0, 1379554642640, 5653700988774, 7799807765976, 4251093775036, 969138751238, 62961757957, 0, 0, 0] := by
  rw [show A10K2.u1014 = KTree.node A10K2.u1012 (nat_lit 15405668) (nat_lit 10800171407) (nat_lit 0) A10K2.u1013 from rfl, totK_node, atot1012, atot1013]
  decide +kernel

theorem arows1025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1025 = true := by
  rw [show A10K2.u1025 = KTree.node A10K2.u1023 (nat_lit 15426861) (nat_lit 5227269692) (nat_lit 0) A10K2.u1024 from rfl, allE_node, arows1023, irow1025, arows1024]
  all_goals rfl

theorem atot1025 : totK PA10K2 A10K2.u1025 = [0, 866947050573, 4509580761357, 8052612410577, 5348425925129, 1045355727520, 38375581520, 0, 0, 0] := by
  rw [show A10K2.u1025 = KTree.node A10K2.u1023 (nat_lit 15426861) (nat_lit 5227269692) (nat_lit 0) A10K2.u1024 from rfl, totK_node, atot1023, atot1024]
  decide +kernel

theorem arows1028 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1028 = true := by
  rw [show A10K2.u1028 = KTree.node A10K2.u1026 (nat_lit 15437790) (nat_lit 14804376456) (nat_lit 0) A10K2.u1027 from rfl, allE_node, arows1026, irow1028, arows1027]
  all_goals rfl

theorem atot1028 : totK PA10K2 A10K2.u1028 = [0, 0, 1620351687487, 6407770398493, 8121753884849, 3451282493525, 369538660082, 6632180018, 0, 0] := by
  rw [show A10K2.u1028 = KTree.node A10K2.u1026 (nat_lit 15437790) (nat_lit 14804376456) (nat_lit 0) A10K2.u1027 from rfl, totK_node, atot1026, atot1027]
  decide +kernel

theorem arows1032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1032 = true := by
  rw [show A10K2.u1032 = KTree.node A10K2.u1030 (nat_lit 15459493) (nat_lit 5830587313) (nat_lit 0) A10K2.u1031 from rfl, allE_node, arows1030, irow1032, arows1031]
  all_goals rfl

theorem atot1032 : totK PA10K2 A10K2.u1032 = [0, 0, 950775798685, 5078871595053, 8466519833010, 4725155916750, 630597599016, 13113983930, 0, 0] := by
  rw [show A10K2.u1032 = KTree.node A10K2.u1030 (nat_lit 15459493) (nat_lit 5830587313) (nat_lit 0) A10K2.u1031 from rfl, totK_node, atot1030, atot1031]
  decide +kernel

theorem arows1035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1035 = true := by
  rw [show A10K2.u1035 = KTree.node A10K2.u1033 (nat_lit 15543305) (nat_lit 5698273843) (nat_lit 0) A10K2.u1034 from rfl, allE_node, arows1033, irow1035, arows1034]
  all_goals rfl

theorem atot1035 : totK PA10K2 A10K2.u1035 = [0, 0, 846871377146, 4258989474401, 7563764081776, 5400678080855, 1300699368876, 86586957493, 0, 0] := by
  rw [show A10K2.u1035 = KTree.node A10K2.u1033 (nat_lit 15543305) (nat_lit 5698273843) (nat_lit 0) A10K2.u1034 from rfl, totK_node, atot1033, atot1034]
  decide +kernel

theorem arows1040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1040 = true := by
  rw [show A10K2.u1040 = KTree.node A10K2.u1038 (nat_lit 15557011) (nat_lit 9926042664) (nat_lit 0) A10K2.u1039 from rfl, allE_node, arows1038, irow1040, arows1039]
  all_goals rfl

theorem atot1040 : totK PA10K2 A10K2.u1040 = [0, 0, 1362400161870, 5908835074818, 8235501597209, 3755489720618, 437614468474, 5982052406, 0, 0] := by
  rw [show A10K2.u1040 = KTree.node A10K2.u1038 (nat_lit 15557011) (nat_lit 9926042664) (nat_lit 0) A10K2.u1039 from rfl, totK_node, atot1038, atot1039]
  decide +kernel

theorem arows1043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1043 = true := by
  rw [show A10K2.u1043 = KTree.node A10K2.u1041 (nat_lit 15575826) (nat_lit 14509021569) (nat_lit 0) A10K2.u1042 from rfl, allE_node, arows1041, irow1043, arows1042]
  all_goals rfl

theorem atot1043 : totK PA10K2 A10K2.u1043 = [0, 0, 0, 1543543482397, 6328851001900, 7972255837456, 3202425887582, 377671234060, 7380853412, 0] := by
  rw [show A10K2.u1043 = KTree.node A10K2.u1041 (nat_lit 15575826) (nat_lit 14509021569) (nat_lit 0) A10K2.u1042 from rfl, totK_node, atot1041, atot1042]
  decide +kernel

theorem arows1047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1047 = true := by
  rw [show A10K2.u1047 = KTree.node A10K2.u1045 (nat_lit 15663104) (nat_lit 15792662511) (nat_lit 0) A10K2.u1046 from rfl, allE_node, arows1045, irow1047, arows1046]
  all_goals rfl

theorem atot1047 : totK PA10K2 A10K2.u1047 = [0, 0, 635471765371, 3875737064691, 8009634533099, 6085771548164, 1297013131082, 62347873231, 0, 0] := by
  rw [show A10K2.u1047 = KTree.node A10K2.u1045 (nat_lit 15663104) (nat_lit 15792662511) (nat_lit 0) A10K2.u1046 from rfl, totK_node, atot1045, atot1046]
  decide +kernel

theorem arows1050 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1050 = true := by
  rw [show A10K2.u1050 = KTree.node A10K2.u1048 (nat_lit 15677141) (nat_lit 6106568767) (nat_lit 0) A10K2.u1049 from rfl, allE_node, arows1048, irow1050, arows1049]
  all_goals rfl

theorem atot1050 : totK PA10K2 A10K2.u1050 = [0, 0, 1422570104615, 5899034392263, 7993253668826, 3910070068018, 547718992048, 12692412833, 0, 0] := by
  rw [show A10K2.u1050 = KTree.node A10K2.u1048 (nat_lit 15677141) (nat_lit 6106568767) (nat_lit 0) A10K2.u1049 from rfl, totK_node, atot1048, atot1049]
  decide +kernel

theorem arows1056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1056 = true := by
  rw [show A10K2.u1056 = KTree.node A10K2.u1054 (nat_lit 15695472) (nat_lit 14179921097) (nat_lit 0) A10K2.u1055 from rfl, allE_node, arows1054, irow1056, arows1055]
  all_goals rfl

theorem atot1056 : totK PA10K2 A10K2.u1056 = [0, 819775609209, 3284388083676, 5184793991872, 5512674219440, 3967967531830, 1001530084013, 62382159641, 0, 0] := by
  rw [show A10K2.u1056 = KTree.node A10K2.u1054 (nat_lit 15695472) (nat_lit 14179921097) (nat_lit 0) A10K2.u1055 from rfl, totK_node, atot1054, atot1055]
  decide +kernel

theorem arows1059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1059 = true := by
  rw [show A10K2.u1059 = KTree.node A10K2.u1057 (nat_lit 16271660) (nat_lit 13552313479) (nat_lit 0) A10K2.u1058 from rfl, allE_node, arows1057, irow1059, arows1058]
  all_goals rfl

theorem atot1059 : totK PA10K2 A10K2.u1059 = [0, 1307532830047, 5506970772713, 7912516062814, 4058927858830, 666315739633, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1059 = KTree.node A10K2.u1057 (nat_lit 16271660) (nat_lit 13552313479) (nat_lit 0) A10K2.u1058 from rfl, totK_node, atot1057, atot1058]
  decide +kernel

theorem arows1063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1063 = true := by
  rw [show A10K2.u1063 = KTree.node A10K2.u1061 (nat_lit 16285659) (nat_lit 5669976202) (nat_lit 0) A10K2.u1062 from rfl, allE_node, arows1061, irow1063, arows1062]
  all_goals rfl

theorem atot1063 : totK PA10K2 A10K2.u1063 = [0, 0, 2102167982431, 7379201435307, 7799388421866, 2414508920945, 162226337990, 0, 0, 0] := by
  rw [show A10K2.u1063 = KTree.node A10K2.u1061 (nat_lit 16285659) (nat_lit 5669976202) (nat_lit 0) A10K2.u1062 from rfl, totK_node, atot1061, atot1062]
  decide +kernel

theorem arows1066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1066 = true := by
  rw [show A10K2.u1066 = KTree.node A10K2.u1064 (nat_lit 16306500) (nat_lit 12564045994) (nat_lit 0) A10K2.u1065 from rfl, allE_node, arows1064, irow1066, arows1065]
  all_goals rfl

theorem atot1066 : totK PA10K2 A10K2.u1066 = [0, 77065070666, 1401222046957, 5758815200938, 8058219975922, 3718676349388, 509755312650, 12477124820, 0, 0] := by
  rw [show A10K2.u1066 = KTree.node A10K2.u1064 (nat_lit 16306500) (nat_lit 12564045994) (nat_lit 0) A10K2.u1065 from rfl, totK_node, atot1064, atot1065]
  decide +kernel

theorem arows1071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1071 = true := by
  rw [show A10K2.u1071 = KTree.node A10K2.u1069 (nat_lit 16332508) (nat_lit 10787050033) (nat_lit 0) A10K2.u1070 from rfl, allE_node, arows1069, irow1071, arows1070]
  all_goals rfl

theorem atot1071 : totK PA10K2 A10K2.u1071 = [0, 1188975773006, 5475249712182, 8114228780133, 4293557942578, 706597503662, 31543789865, 0, 0, 0] := by
  rw [show A10K2.u1071 = KTree.node A10K2.u1069 (nat_lit 16332508) (nat_lit 10787050033) (nat_lit 0) A10K2.u1070 from rfl, totK_node, atot1069, atot1070]
  decide +kernel

theorem arows1074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1074 = true := by
  rw [show A10K2.u1074 = KTree.node A10K2.u1072 (nat_lit 16348572) (nat_lit 8553532269) (nat_lit 0) A10K2.u1073 from rfl, allE_node, arows1072, irow1074, arows1073]
  all_goals rfl

theorem atot1074 : totK PA10K2 A10K2.u1074 = [0, 610252771174, 3739693751150, 7751092903890, 6218817659290, 1595959403505, 95049001292, 0, 0, 0] := by
  rw [show A10K2.u1074 = KTree.node A10K2.u1072 (nat_lit 16348572) (nat_lit 8553532269) (nat_lit 0) A10K2.u1073 from rfl, totK_node, atot1072, atot1073]
  decide +kernel

theorem arows1078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1078 = true := by
  rw [show A10K2.u1078 = KTree.node A10K2.u1076 (nat_lit 16369139) (nat_lit 9015180604) (nat_lit 0) A10K2.u1077 from rfl, allE_node, arows1076, irow1078, arows1077]
  all_goals rfl

theorem atot1078 : totK PA10K2 A10K2.u1078 = [0, 0, 1320117251233, 5792490894836, 8201873065058, 3950106405757, 530596635349, 12696458652, 0, 0] := by
  rw [show A10K2.u1078 = KTree.node A10K2.u1076 (nat_lit 16369139) (nat_lit 9015180604) (nat_lit 0) A10K2.u1077 from rfl, totK_node, atot1076, atot1077]
  decide +kernel

theorem arows1081 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1081 = true := by
  rw [show A10K2.u1081 = KTree.node A10K2.u1079 (nat_lit 16453987) (nat_lit 1021538940) (nat_lit 0) A10K2.u1080 from rfl, allE_node, arows1079, irow1081, arows1080]
  all_goals rfl

theorem atot1081 : totK PA10K2 A10K2.u1081 = [0, 1344456871382, 5447177752663, 7499466285999, 4140169077156, 937149285356, 62035974063, 0, 0, 0] := by
  rw [show A10K2.u1081 = KTree.node A10K2.u1079 (nat_lit 16453987) (nat_lit 1021538940) (nat_lit 0) A10K2.u1080 from rfl, totK_node, atot1079, atot1080]
  decide +kernel

theorem arows1088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1088 = true := by
  rw [show A10K2.u1088 = KTree.node A10K2.u1086 (nat_lit 16474590) (nat_lit 15060741965) (nat_lit 0) A10K2.u1087 from rfl, allE_node, arows1086, irow1088, arows1087]
  all_goals rfl

theorem atot1088 : totK PA10K2 A10K2.u1088 = [0, 1029302401414, 5093735992314, 8160499094741, 4673162969976, 794182043229, 24608236885, 0, 0, 0] := by
  rw [show A10K2.u1088 = KTree.node A10K2.u1086 (nat_lit 16474590) (nat_lit 15060741965) (nat_lit 0) A10K2.u1087 from rfl, totK_node, atot1086, atot1087]
  decide +kernel

theorem arows1091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1091 = true := by
  rw [show A10K2.u1091 = KTree.node A10K2.u1089 (nat_lit 16484452) (nat_lit 10984676122) (nat_lit 0) A10K2.u1090 from rfl, allE_node, arows1089, irow1091, arows1090]
  all_goals rfl

theorem atot1091 : totK PA10K2 A10K2.u1091 = [0, 0, 1489207746623, 6196292357418, 8161475208264, 3472669581406, 375646858279, 6904928264, 0, 0] := by
  rw [show A10K2.u1091 = KTree.node A10K2.u1089 (nat_lit 16484452) (nat_lit 10984676122) (nat_lit 0) A10K2.u1090 from rfl, totK_node, atot1089, atot1090]
  decide +kernel

theorem arows1095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1095 = true := by
  rw [show A10K2.u1095 = KTree.node A10K2.u1093 (nat_lit 16496827) (nat_lit 6989774804) (nat_lit 0) A10K2.u1094 from rfl, allE_node, arows1093, irow1095, arows1094]
  all_goals rfl

theorem atot1095 : totK PA10K2 A10K2.u1095 = [0, 0, 1505926345019, 6273784965311, 8054570652655, 3397504452176, 353293867515, 7047025452, 0, 0] := by
  rw [show A10K2.u1095 = KTree.node A10K2.u1093 (nat_lit 16496827) (nat_lit 6989774804) (nat_lit 0) A10K2.u1094 from rfl, totK_node, atot1093, atot1094]
  decide +kernel

theorem arows1098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1098 = true := by
  rw [show A10K2.u1098 = KTree.node A10K2.u1096 (nat_lit 16515332) (nat_lit 12865384108) (nat_lit 0) A10K2.u1097 from rfl, allE_node, arows1096, irow1098, arows1097]
  all_goals rfl

theorem atot1098 : totK PA10K2 A10K2.u1098 = [0, 0, 817736212206, 4272927294018, 7722965607862, 5474786660123, 1258006955718, 73587250926, 0, 0] := by
  rw [show A10K2.u1098 = KTree.node A10K2.u1096 (nat_lit 16515332) (nat_lit 12865384108) (nat_lit 0) A10K2.u1097 from rfl, totK_node, atot1096, atot1097]
  decide +kernel

theorem arows1103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1103 = true := by
  rw [show A10K2.u1103 = KTree.node A10K2.u1101 (nat_lit 16537891) (nat_lit 9520342031) (nat_lit 0) A10K2.u1102 from rfl, allE_node, arows1101, irow1103, arows1102]
  all_goals rfl

theorem atot1103 : totK PA10K2 A10K2.u1103 = [0, 0, 1304415440809, 5837133708788, 8336504484228, 3802948021274, 375125796242, 0, 0, 0] := by
  rw [show A10K2.u1103 = KTree.node A10K2.u1101 (nat_lit 16537891) (nat_lit 9520342031) (nat_lit 0) A10K2.u1102 from rfl, totK_node, atot1101, atot1102]
  decide +kernel

theorem arows1106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1106 = true := by
  rw [show A10K2.u1106 = KTree.node A10K2.u1104 (nat_lit 16549942) (nat_lit 15043555810) (nat_lit 0) A10K2.u1105 from rfl, allE_node, arows1104, irow1106, arows1105]
  all_goals rfl

theorem atot1106 : totK PA10K2 A10K2.u1106 = [0, 0, 0, 1547325798731, 6502865380480, 8253792504421, 3089994352283, 305829260107, 6725424603, 0] := by
  rw [show A10K2.u1106 = KTree.node A10K2.u1104 (nat_lit 16549942) (nat_lit 15043555810) (nat_lit 0) A10K2.u1105 from rfl, totK_node, atot1104, atot1105]
  decide +kernel

theorem arows1110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1110 = true := by
  rw [show A10K2.u1110 = KTree.node A10K2.u1108 (nat_lit 16576441) (nat_lit 6821941981) (nat_lit 0) A10K2.u1109 from rfl, allE_node, arows1108, irow1110, arows1109]
  all_goals rfl

theorem atot1110 : totK PA10K2 A10K2.u1110 = [0, 0, 780638625629, 4270030616898, 7951202935479, 5572520131110, 1202155489095, 68492179993, 0, 0] := by
  rw [show A10K2.u1110 = KTree.node A10K2.u1108 (nat_lit 16576441) (nat_lit 6821941981) (nat_lit 0) A10K2.u1109 from rfl, totK_node, atot1108, atot1109]
  decide +kernel

theorem arows1113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1113 = true := by
  rw [show A10K2.u1113 = KTree.node A10K2.u1111 (nat_lit 16605733) (nat_lit 3073853131) (nat_lit 0) A10K2.u1112 from rfl, allE_node, arows1111, irow1113, arows1112]
  all_goals rfl

theorem atot1113 : totK PA10K2 A10K2.u1113 = [0, 0, 1091879829829, 5135712453926, 8182660302010, 4754125944809, 755529132667, 18976310536, 0, 0] := by
  rw [show A10K2.u1113 = KTree.node A10K2.u1111 (nat_lit 16605733) (nat_lit 3073853131) (nat_lit 0) A10K2.u1112 from rfl, totK_node, atot1111, atot1112]
  decide +kernel

theorem arows1119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1119 = true := by
  rw [show A10K2.u1119 = KTree.node A10K2.u1117 (nat_lit 16624795) (nat_lit 9975195466) (nat_lit 0) A10K2.u1118 from rfl, allE_node, arows1117, irow1119, arows1118]
  all_goals rfl

theorem atot1119 : totK PA10K2 A10K2.u1119 = [0, 0, 0, 1690904763485, 6663142930751, 8164470501391, 3056385270413, 310755221914, 6860445330, 0] := by
  rw [show A10K2.u1119 = KTree.node A10K2.u1117 (nat_lit 16624795) (nat_lit 9975195466) (nat_lit 0) A10K2.u1118 from rfl, totK_node, atot1117, atot1118]
  decide +kernel

theorem arows1122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1122 = true := by
  rw [show A10K2.u1122 = KTree.node A10K2.u1120 (nat_lit 16713760) (nat_lit 13959179896) (nat_lit 0) A10K2.u1121 from rfl, allE_node, arows1120, irow1122, arows1121]
  all_goals rfl

theorem atot1122 : totK PA10K2 A10K2.u1122 = [0, 0, 760685406009, 4112770434491, 7658754605933, 5653340557882, 1352414792243, 80341524651, 0, 0] := by
  rw [show A10K2.u1122 = KTree.node A10K2.u1120 (nat_lit 16713760) (nat_lit 13959179896) (nat_lit 0) A10K2.u1121 from rfl, totK_node, atot1120, atot1121]
  decide +kernel

theorem arows1126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1126 = true := by
  rw [show A10K2.u1126 = KTree.node A10K2.u1124 (nat_lit 16725778) (nat_lit 15022861319) (nat_lit 0) A10K2.u1125 from rfl, allE_node, arows1124, irow1126, arows1125]
  all_goals rfl

theorem atot1126 : totK PA10K2 A10K2.u1126 = [0, 0, 1495492748910, 5961295115361, 7814446780174, 3756065947073, 485762786178, 11918539728, 0, 0] := by
  rw [show A10K2.u1126 = KTree.node A10K2.u1124 (nat_lit 16725778) (nat_lit 15022861319) (nat_lit 0) A10K2.u1125 from rfl, totK_node, atot1124, atot1125]
  decide +kernel

theorem arows1129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1129 = true := by
  rw [show A10K2.u1129 = KTree.node A10K2.u1127 (nat_lit 16744087) (nat_lit 14036657062) (nat_lit 0) A10K2.u1128 from rfl, allE_node, arows1127, irow1129, arows1128]
  all_goals rfl

theorem atot1129 : totK PA10K2 A10K2.u1129 = [0, 0, 122956571035, 2343798814402, 7305401820834, 7562980378608, 2282796590364, 149664496022, 0, 0] := by
  rw [show A10K2.u1129 = KTree.node A10K2.u1127 (nat_lit 16744087) (nat_lit 14036657062) (nat_lit 0) A10K2.u1128 from rfl, totK_node, atot1127, atot1128]
  decide +kernel

theorem arows1134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1134 = true := by
  rw [show A10K2.u1134 = KTree.node A10K2.u1132 (nat_lit 16756671) (nat_lit 14263530493) (nat_lit 0) A10K2.u1133 from rfl, allE_node, arows1132, irow1134, arows1133]
  all_goals rfl

theorem atot1134 : totK PA10K2 A10K2.u1134 = [0, 0, 0, 1272610563077, 5693665967644, 8103257813387, 3796128772086, 495048342578, 12758098799, 0] := by
  rw [show A10K2.u1134 = KTree.node A10K2.u1132 (nat_lit 16756671) (nat_lit 14263530493) (nat_lit 0) A10K2.u1133 from rfl, totK_node, atot1132, atot1133]
  decide +kernel

theorem arows1137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1137 = true := by
  rw [show A10K2.u1137 = KTree.node A10K2.u1135 (nat_lit 16776624) (nat_lit 14258471646) (nat_lit 0) A10K2.u1136 from rfl, allE_node, arows1135, irow1137, arows1136]
  all_goals rfl

theorem atot1137 : totK PA10K2 A10K2.u1137 = [0, 874031059315, 3015030631522, 3332166803619, 2919983068905, 4689125766083, 3774324470736, 961189328672, 61018386929, 0] := by
  rw [show A10K2.u1137 = KTree.node A10K2.u1135 (nat_lit 16776624) (nat_lit 14258471646) (nat_lit 0) A10K2.u1136 from rfl, totK_node, atot1135, atot1136]
  decide +kernel

theorem arows1141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1141 = true := by
  rw [show A10K2.u1141 = KTree.node A10K2.u1139 (nat_lit 16794161) (nat_lit 9952319228) (nat_lit 0) A10K2.u1140 from rfl, allE_node, arows1139, irow1141, arows1140]
  all_goals rfl

theorem atot1141 : totK PA10K2 A10K2.u1141 = [0, 722046948357, 4388359262065, 8124164414416, 4823662064701, 760452436607, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1141 = KTree.node A10K2.u1139 (nat_lit 16794161) (nat_lit 9952319228) (nat_lit 0) A10K2.u1140 from rfl, totK_node, atot1139, atot1140]
  decide +kernel

theorem arows1144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1144 = true := by
  rw [show A10K2.u1144 = KTree.node A10K2.u1142 (nat_lit 16806328) (nat_lit 14479854271) (nat_lit 0) A10K2.u1143 from rfl, allE_node, arows1142, irow1144, arows1143]
  all_goals rfl

theorem atot1144 : totK PA10K2 A10K2.u1144 = [0, 783957388807, 4091371870420, 7625595256714, 5887815645621, 1531801747300, 85906858087, 0, 0, 0] := by
  rw [show A10K2.u1144 = KTree.node A10K2.u1142 (nat_lit 16806328) (nat_lit 14479854271) (nat_lit 0) A10K2.u1143 from rfl, totK_node, atot1142, atot1143]
  decide +kernel

theorem arows1152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1152 = true := by
  rw [show A10K2.u1152 = KTree.node A10K2.u1150 (nat_lit 16816904) (nat_lit 12416319108) (nat_lit 0) A10K2.u1151 from rfl, allE_node, arows1150, irow1152, arows1151]
  all_goals rfl

theorem atot1152 : totK PA10K2 A10K2.u1152 = [0, 0, 1164287173907, 5452958542756, 7856834636464, 3703990873379, 613813254158, 30650496230, 0, 0] := by
  rw [show A10K2.u1152 = KTree.node A10K2.u1150 (nat_lit 16816904) (nat_lit 12416319108) (nat_lit 0) A10K2.u1151 from rfl, totK_node, atot1150, atot1151]
  decide +kernel

theorem arows1155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1155 = true := by
  rw [show A10K2.u1155 = KTree.node A10K2.u1153 (nat_lit 16838180) (nat_lit 8697865253) (nat_lit 0) A10K2.u1154 from rfl, allE_node, arows1153, irow1155, arows1154]
  all_goals rfl

theorem atot1155 : totK PA10K2 A10K2.u1155 = [0, 801319042366, 3820756501616, 6778201807333, 5796880816364, 2164010869838, 240661066276, 5546304973, 0, 0] := by
  rw [show A10K2.u1155 = KTree.node A10K2.u1153 (nat_lit 16838180) (nat_lit 8697865253) (nat_lit 0) A10K2.u1154 from rfl, totK_node, atot1153, atot1154]
  decide +kernel

theorem arows1159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1159 = true := by
  rw [show A10K2.u1159 = KTree.node A10K2.u1157 (nat_lit 16919314) (nat_lit 14509021569) (nat_lit 0) A10K2.u1158 from rfl, allE_node, arows1157, irow1159, arows1158]
  all_goals rfl

theorem atot1159 : totK PA10K2 A10K2.u1159 = [0, 1000359693236, 4529458762280, 7375188352929, 4674091595968, 904277590901, 42259512619, 0, 0, 0] := by
  rw [show A10K2.u1159 = KTree.node A10K2.u1157 (nat_lit 16919314) (nat_lit 14509021569) (nat_lit 0) A10K2.u1158 from rfl, totK_node, atot1157, atot1158]
  decide +kernel

theorem arows1162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1162 = true := by
  rw [show A10K2.u1162 = KTree.node A10K2.u1160 (nat_lit 16941619) (nat_lit 3282019674) (nat_lit 0) A10K2.u1161 from rfl, allE_node, arows1160, irow1162, arows1161]
  all_goals rfl

theorem atot1162 : totK PA10K2 A10K2.u1162 = [0, 198880611318, 2950271308705, 7797854772158, 6419751816492, 1407639247916, 57019069441, 0, 0, 0] := by
  rw [show A10K2.u1162 = KTree.node A10K2.u1160 (nat_lit 16941619) (nat_lit 3282019674) (nat_lit 0) A10K2.u1161 from rfl, totK_node, atot1160, atot1161]
  decide +kernel

theorem arows1167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1167 = true := by
  rw [show A10K2.u1167 = KTree.node A10K2.u1165 (nat_lit 16962902) (nat_lit 7328155110) (nat_lit 0) A10K2.u1166 from rfl, allE_node, arows1165, irow1167, arows1166]
  all_goals rfl

theorem atot1167 : totK PA10K2 A10K2.u1167 = [0, 814612738366, 3516141871912, 6218210997830, 5755508437132, 2160386864388, 265260643001, 6354482628, 0, 0] := by
  rw [show A10K2.u1167 = KTree.node A10K2.u1165 (nat_lit 16962902) (nat_lit 7328155110) (nat_lit 0) A10K2.u1166 from rfl, totK_node, atot1165, atot1166]
  decide +kernel

theorem arows1170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1170 = true := by
  rw [show A10K2.u1170 = KTree.node A10K2.u1168 (nat_lit 16985265) (nat_lit 6174112270) (nat_lit 0) A10K2.u1169 from rfl, allE_node, arows1168, irow1170, arows1169]
  all_goals rfl

theorem atot1170 : totK PA10K2 A10K2.u1170 = [0, 990120236774, 4944062755045, 8233691682421, 5014673807073, 897447705623, 38858708962, 0, 0, 0] := by
  rw [show A10K2.u1170 = KTree.node A10K2.u1168 (nat_lit 16985265) (nat_lit 6174112270) (nat_lit 0) A10K2.u1169 from rfl, totK_node, atot1168, atot1169]
  decide +kernel

theorem arows1174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1174 = true := by
  rw [show A10K2.u1174 = KTree.node A10K2.u1172 (nat_lit 17005747) (nat_lit 10050457215) (nat_lit 0) A10K2.u1173 from rfl, allE_node, arows1172, irow1174, arows1173]
  all_goals rfl

theorem atot1174 : totK PA10K2 A10K2.u1174 = [0, 323642880550, 3023565690989, 7758998223819, 6828656241855, 1780062907164, 100872565648, 0, 0, 0] := by
  rw [show A10K2.u1174 = KTree.node A10K2.u1172 (nat_lit 17005747) (nat_lit 10050457215) (nat_lit 0) A10K2.u1173 from rfl, totK_node, atot1172, atot1173]
  decide +kernel

theorem arows1177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1177 = true := by
  rw [show A10K2.u1177 = KTree.node A10K2.u1175 (nat_lit 17018438) (nat_lit 15051240479) (nat_lit 0) A10K2.u1176 from rfl, allE_node, arows1175, irow1177, arows1176]
  all_goals rfl

theorem atot1177 : totK PA10K2 A10K2.u1177 = [0, 0, 1146418129020, 5421694918863, 8501197098548, 4423904576512, 525379042441, 6904928264, 0, 0] := by
  rw [show A10K2.u1177 = KTree.node A10K2.u1175 (nat_lit 17018438) (nat_lit 15051240479) (nat_lit 0) A10K2.u1176 from rfl, totK_node, atot1175, atot1176]
  decide +kernel

theorem arows1183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1183 = true := by
  rw [show A10K2.u1183 = KTree.node A10K2.u1181 (nat_lit 17039061) (nat_lit 2218540613) (nat_lit 0) A10K2.u1182 from rfl, allE_node, arows1181, irow1183, arows1182]
  all_goals rfl

theorem atot1183 : totK PA10K2 A10K2.u1183 = [0, 0, 1036996271002, 4955984022316, 7836526866868, 4802066915500, 987426950550, 47331038410, 0, 0] := by
  rw [show A10K2.u1183 = KTree.node A10K2.u1181 (nat_lit 17039061) (nat_lit 2218540613) (nat_lit 0) A10K2.u1182 from rfl, totK_node, atot1181, atot1182]
  decide +kernel

theorem arows1186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1186 = true := by
  rw [show A10K2.u1186 = KTree.node A10K2.u1184 (nat_lit 17056997) (nat_lit 7023573905) (nat_lit 0) A10K2.u1185 from rfl, allE_node, arows1184, irow1186, arows1185]
  all_goals rfl

theorem atot1186 : totK PA10K2 A10K2.u1186 = [0, 0, 923351697140, 4574641478613, 7752444212981, 4517667008971, 781959882788, 36536693801, 0, 0] := by
  rw [show A10K2.u1186 = KTree.node A10K2.u1184 (nat_lit 17056997) (nat_lit 7023573905) (nat_lit 0) A10K2.u1185 from rfl, totK_node, atot1184, atot1185]
  decide +kernel

theorem arows1190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1190 = true := by
  rw [show A10K2.u1190 = KTree.node A10K2.u1188 (nat_lit 17069461) (nat_lit 1321715390) (nat_lit 0) A10K2.u1189 from rfl, allE_node, arows1188, irow1190, arows1189]
  all_goals rfl

theorem atot1190 : totK PA10K2 A10K2.u1190 = [0, 0, 581035684948, 3917549193729, 8096279994311, 5889904678276, 1260963410392, 66253585394, 0, 0] := by
  rw [show A10K2.u1190 = KTree.node A10K2.u1188 (nat_lit 17069461) (nat_lit 1321715390) (nat_lit 0) A10K2.u1189 from rfl, totK_node, atot1188, atot1189]
  decide +kernel

theorem arows1193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1193 = true := by
  rw [show A10K2.u1193 = KTree.node A10K2.u1191 (nat_lit 17088952) (nat_lit 14365455101) (nat_lit 0) A10K2.u1192 from rfl, allE_node, arows1191, irow1193, arows1192]
  all_goals rfl

theorem atot1193 : totK PA10K2 A10K2.u1193 = [0, 0, 0, 810884501059, 4688675244241, 7922775827339, 4170794038780, 678602052010, 30605747850, 0] := by
  rw [show A10K2.u1193 = KTree.node A10K2.u1191 (nat_lit 17088952) (nat_lit 14365455101) (nat_lit 0) A10K2.u1192 from rfl, totK_node, atot1191, atot1192]
  decide +kernel

theorem arows1198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1198 = true := by
  rw [show A10K2.u1198 = KTree.node A10K2.u1196 (nat_lit 17172481) (nat_lit 10503824933) (nat_lit 0) A10K2.u1197 from rfl, allE_node, arows1196, irow1198, arows1197]
  all_goals rfl

theorem atot1198 : totK PA10K2 A10K2.u1198 = [0, 0, 801142926959, 4277767473597, 7739488156460, 5277457531604, 1323677615741, 162848774107, 5528811039, 0] := by
  rw [show A10K2.u1198 = KTree.node A10K2.u1196 (nat_lit 17172481) (nat_lit 10503824933) (nat_lit 0) A10K2.u1197 from rfl, totK_node, atot1196, atot1197]
  decide +kernel

theorem arows1201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1201 = true := by
  rw [show A10K2.u1201 = KTree.node A10K2.u1199 (nat_lit 17187170) (nat_lit 11027884739) (nat_lit 0) A10K2.u1200 from rfl, allE_node, arows1199, irow1201, arows1200]
  all_goals rfl

theorem atot1201 : totK PA10K2 A10K2.u1201 = [0, 0, 1198290300191, 5541245111672, 7839212810310, 3393592393810, 361620776500, 11494708454, 0, 0] := by
  rw [show A10K2.u1201 = KTree.node A10K2.u1199 (nat_lit 17187170) (nat_lit 11027884739) (nat_lit 0) A10K2.u1200 from rfl, totK_node, atot1199, atot1200]
  decide +kernel

theorem arows1205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1205 = true := by
  rw [show A10K2.u1205 = KTree.node A10K2.u1203 (nat_lit 17212577) (nat_lit 4384323452) (nat_lit 2) A10K2.u1204 from rfl, allE_node, arows1203, irow1205, arows1204]
  all_goals rfl

theorem atot1205 : totK PA10K2 A10K2.u1205 = [0, 0, 0, 2179299737069, 7668224694875, 7051770355319, 1531322891523, 81783304252, 0, 0] := by
  rw [show A10K2.u1205 = KTree.node A10K2.u1203 (nat_lit 17212577) (nat_lit 4384323452) (nat_lit 2) A10K2.u1204 from rfl, totK_node, atot1203, atot1204]
  decide +kernel

theorem arows1208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1208 = true := by
  rw [show A10K2.u1208 = KTree.node A10K2.u1206 (nat_lit 17238824) (nat_lit 11603191138) (nat_lit 0) A10K2.u1207 from rfl, allE_node, arows1206, irow1208, arows1207]
  all_goals rfl

theorem atot1208 : totK PA10K2 A10K2.u1208 = [0, 0, 999439602828, 4203060639840, 6745512574579, 5269514483457, 1791816381401, 217603257819, 5676195732, 0] := by
  rw [show A10K2.u1208 = KTree.node A10K2.u1206 (nat_lit 17238824) (nat_lit 11603191138) (nat_lit 0) A10K2.u1207 from rfl, totK_node, atot1206, atot1207]
  decide +kernel

theorem arows1215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1215 = true := by
  rw [show A10K2.u1215 = KTree.node A10K2.u1213 (nat_lit 17261795) (nat_lit 6815601616) (nat_lit 0) A10K2.u1214 from rfl, allE_node, arows1213, irow1215, arows1214]
  all_goals rfl

theorem atot1215 : totK PA10K2 A10K2.u1215 = [0, 0, 1124540638475, 5427386587483, 8420545672874, 4510444605773, 613415155508, 6853348008, 0, 0] := by
  rw [show A10K2.u1215 = KTree.node A10K2.u1213 (nat_lit 17261795) (nat_lit 6815601616) (nat_lit 0) A10K2.u1214 from rfl, totK_node, atot1213, atot1214]
  decide +kernel

theorem arows1218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1218 = true := by
  rw [show A10K2.u1218 = KTree.node A10K2.u1216 (nat_lit 17829261) (nat_lit 4360216829) (nat_lit 0) A10K2.u1217 from rfl, allE_node, arows1216, irow1218, arows1217]
  all_goals rfl

theorem atot1218 : totK PA10K2 A10K2.u1218 = [0, 1054409893898, 4431723651720, 6644354714382, 4649294788330, 1999706522823, 554882625011, 41417404726, 0, 0] := by
  rw [show A10K2.u1218 = KTree.node A10K2.u1216 (nat_lit 17829261) (nat_lit 4360216829) (nat_lit 0) A10K2.u1217 from rfl, totK_node, atot1216, atot1217]
  decide +kernel

theorem arows1222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1222 = true := by
  rw [show A10K2.u1222 = KTree.node A10K2.u1220 (nat_lit 17848481) (nat_lit 8190907844) (nat_lit 0) A10K2.u1221 from rfl, allE_node, arows1220, irow1222, arows1221]
  all_goals rfl

theorem atot1222 : totK PA10K2 A10K2.u1222 = [0, 1137063831772, 5451428204929, 8255807098774, 3978882409635, 480081731627, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1222 = KTree.node A10K2.u1220 (nat_lit 17848481) (nat_lit 8190907844) (nat_lit 0) A10K2.u1221 from rfl, totK_node, atot1220, atot1221]
  decide +kernel

theorem arows1225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1225 = true := by
  rw [show A10K2.u1225 = KTree.node A10K2.u1223 (nat_lit 17861728) (nat_lit 13857200976) (nat_lit 0) A10K2.u1224 from rfl, allE_node, arows1223, irow1225, arows1224]
  all_goals rfl

theorem atot1225 : totK PA10K2 A10K2.u1225 = [0, 0, 1341985494514, 5620370848620, 7841348296474, 3837531278796, 629189880677, 30650496230, 0, 0] := by
  rw [show A10K2.u1225 = KTree.node A10K2.u1223 (nat_lit 17861728) (nat_lit 13857200976) (nat_lit 0) A10K2.u1224 from rfl, totK_node, atot1223, atot1224]
  decide +kernel

theorem arows1230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1230 = true := by
  rw [show A10K2.u1230 = KTree.node A10K2.u1228 (nat_lit 17881373) (nat_lit 6410327068) (nat_lit 0) A10K2.u1229 from rfl, allE_node, arows1228, irow1230, arows1229]
  all_goals rfl

theorem atot1230 : totK PA10K2 A10K2.u1230 = [0, 293929698888, 2142443114854, 6210739081104, 7421245097764, 2883632199187, 293312577101, 5546304973, 0, 0] := by
  rw [show A10K2.u1230 = KTree.node A10K2.u1228 (nat_lit 17881373) (nat_lit 6410327068) (nat_lit 0) A10K2.u1229 from rfl, totK_node, atot1228, atot1229]
  decide +kernel

theorem arows1233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1233 = true := by
  rw [show A10K2.u1233 = KTree.node A10K2.u1231 (nat_lit 17909089) (nat_lit 8212835464) (nat_lit 0) A10K2.u1232 from rfl, allE_node, arows1231, irow1233, arows1232]
  all_goals rfl

theorem atot1233 : totK PA10K2 A10K2.u1233 = [0, 1007974306833, 5140140038691, 8156985839246, 4095547064839, 552155192238, 12388698189, 0, 0, 0] := by
  rw [show A10K2.u1233 = KTree.node A10K2.u1231 (nat_lit 17909089) (nat_lit 8212835464) (nat_lit 0) A10K2.u1232 from rfl, totK_node, atot1231, atot1232]
  decide +kernel

theorem arows1237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1237 = true := by
  rw [show A10K2.u1237 = KTree.node A10K2.u1235 (nat_lit 17942693) (nat_lit 7333572875) (nat_lit 0) A10K2.u1236 from rfl, allE_node, arows1235, irow1237, arows1236]
  all_goals rfl

theorem atot1237 : totK PA10K2 A10K2.u1237 = [0, 313543329064, 2280839229448, 6347417998759, 7103545070891, 2580218840212, 277054802505, 6121173289, 0, 0] := by
  rw [show A10K2.u1237 = KTree.node A10K2.u1235 (nat_lit 17942693) (nat_lit 7333572875) (nat_lit 0) A10K2.u1236 from rfl, totK_node, atot1235, atot1236]
  decide +kernel

theorem arows1240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1240 = true := by
  rw [show A10K2.u1240 = KTree.node A10K2.u1238 (nat_lit 17963840) (nat_lit 13423509569) (nat_lit 0) A10K2.u1239 from rfl, allE_node, arows1238, irow1240, arows1239]
  all_goals rfl

theorem atot1240 : totK PA10K2 A10K2.u1240 = [0, 1025027536992, 4894180598549, 7668829017175, 4484133494671, 904770920353, 56566207178, 0, 0, 0] := by
  rw [show A10K2.u1240 = KTree.node A10K2.u1238 (nat_lit 17963840) (nat_lit 13423509569) (nat_lit 0) A10K2.u1239 from rfl, totK_node, atot1238, atot1239]
  decide +kernel

theorem arows1246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1246 = true := by
  rw [show A10K2.u1246 = KTree.node A10K2.u1244 (nat_lit 17975848) (nat_lit 12474264402) (nat_lit 0) A10K2.u1245 from rfl, allE_node, arows1244, irow1246, arows1245]
  all_goals rfl

theorem atot1246 : totK PA10K2 A10K2.u1246 = [0, 821967029087, 4471027740847, 7785453120305, 4727316614480, 863501627635, 38021971230, 0, 0, 0] := by
  rw [show A10K2.u1246 = KTree.node A10K2.u1244 (nat_lit 17975848) (nat_lit 12474264402) (nat_lit 0) A10K2.u1245 from rfl, totK_node, atot1244, atot1245]
  decide +kernel

theorem arows1249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1249 = true := by
  rw [show A10K2.u1249 = KTree.node A10K2.u1247 (nat_lit 18006048) (nat_lit 14200915603) (nat_lit 0) A10K2.u1248 from rfl, allE_node, arows1247, irow1249, arows1248]
  all_goals rfl

theorem atot1249 : totK PA10K2 A10K2.u1249 = [0, 0, 1763917702407, 6971834752957, 7740898977293, 2167081408581, 142503590785, 0, 0, 0] := by
  rw [show A10K2.u1249 = KTree.node A10K2.u1247 (nat_lit 18006048) (nat_lit 14200915603) (nat_lit 0) A10K2.u1248 from rfl, totK_node, atot1247, atot1248]
  decide +kernel

theorem arows1253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1253 = true := by
  rw [show A10K2.u1253 = KTree.node A10K2.u1251 (nat_lit 18091397) (nat_lit 4571245602) (nat_lit 0) A10K2.u1252 from rfl, allE_node, arows1251, irow1253, arows1252]
  all_goals rfl

theorem atot1253 : totK PA10K2 A10K2.u1253 = [0, 0, 1054409893898, 4864481167809, 7736779484284, 4496357627835, 819175191828, 37172849495, 0, 0] := by
  rw [show A10K2.u1253 = KTree.node A10K2.u1251 (nat_lit 18091397) (nat_lit 4571245602) (nat_lit 0) A10K2.u1252 from rfl, totK_node, atot1251, atot1252]
  decide +kernel

theorem arows1256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1256 = true := by
  rw [show A10K2.u1256 = KTree.node A10K2.u1254 (nat_lit 18110678) (nat_lit 7303421717) (nat_lit 0) A10K2.u1255 from rfl, allE_node, arows1254, irow1256, arows1255]
  all_goals rfl

theorem atot1256 : totK PA10K2 A10K2.u1256 = [0, 0, 1137063831772, 5441963404868, 8196840460887, 3926389403894, 496360690594, 13207830636, 0, 0] := by
  rw [show A10K2.u1256 = KTree.node A10K2.u1254 (nat_lit 18110678) (nat_lit 7303421717) (nat_lit 0) A10K2.u1255 from rfl, totK_node, atot1254, atot1255]
  decide +kernel

theorem arows1261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1261 = true := by
  rw [show A10K2.u1261 = KTree.node A10K2.u1259 (nat_lit 18168065) (nat_lit 8993844055) (nat_lit 0) A10K2.u1260 from rfl, allE_node, arows1259, irow1261, arows1260]
  all_goals rfl

theorem atot1261 : totK PA10K2 A10K2.u1261 = [0, 0, 1299274360047, 5769909286657, 8102133918909, 3592551571520, 403161321109, 5718040558, 0, 0] := by
  rw [show A10K2.u1261 = KTree.node A10K2.u1259 (nat_lit 18168065) (nat_lit 8993844055) (nat_lit 0) A10K2.u1260 from rfl, totK_node, atot1259, atot1260]
  decide +kernel

theorem arows1264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1264 = true := by
  rw [show A10K2.u1264 = KTree.node A10K2.u1262 (nat_lit 18222128) (nat_lit 14933896366) (nat_lit 0) A10K2.u1263 from rfl, allE_node, arows1262, irow1264, arows1263]
  all_goals rfl

theorem atot1264 : totK PA10K2 A10K2.u1264 = [0, 0, 1006678673835, 4821981747157, 7811188947561, 4407617779757, 755324272255, 36429366174, 0, 0] := by
  rw [show A10K2.u1264 = KTree.node A10K2.u1262 (nat_lit 18222128) (nat_lit 14933896366) (nat_lit 0) A10K2.u1263 from rfl, totK_node, atot1262, atot1263]
  decide +kernel

theorem arows1268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1268 = true := by
  rw [show A10K2.u1268 = KTree.node A10K2.u1266 (nat_lit 18235975) (nat_lit 8513673257) (nat_lit 0) A10K2.u1267 from rfl, allE_node, arows1266, irow1268, arows1267]
  all_goals rfl

theorem atot1268 : totK PA10K2 A10K2.u1268 = [0, 0, 1163893791019, 5575258960416, 8048670663460, 3364440292066, 346780899965, 6034215561, 0, 0] := by
  rw [show A10K2.u1268 = KTree.node A10K2.u1266 (nat_lit 18235975) (nat_lit 8513673257) (nat_lit 0) A10K2.u1267 from rfl, totK_node, atot1266, atot1267]
  decide +kernel

theorem arows1271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1271 = true := by
  rw [show A10K2.u1271 = KTree.node A10K2.u1269 (nat_lit 18261463) (nat_lit 10661619398) (nat_lit 0) A10K2.u1270 from rfl, allE_node, arows1269, irow1271, arows1270]
  all_goals rfl

theorem atot1271 : totK PA10K2 A10K2.u1271 = [0, 0, 0, 2311947540272, 7878243090966, 6778159625493, 1461578351203, 74461528785, 0, 0] := by
  rw [show A10K2.u1271 = KTree.node A10K2.u1269 (nat_lit 18261463) (nat_lit 10661619398) (nat_lit 0) A10K2.u1270 from rfl, totK_node, atot1269, atot1270]
  decide +kernel

theorem arows1280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1280 = true := by
  rw [show A10K2.u1280 = KTree.node A10K2.u1278 (nat_lit 18352684) (nat_lit 12978129887) (nat_lit 0) A10K2.u1279 from rfl, allE_node, arows1278, irow1280, arows1279]
  all_goals rfl

theorem atot1280 : totK PA10K2 A10K2.u1280 = [0, 844183794776, 3813434194501, 5766453824869, 4111126021418, 2889838348829, 1359961360083, 195382007035, 6354482628, 0] := by
  rw [show A10K2.u1280 = KTree.node A10K2.u1278 (nat_lit 18352684) (nat_lit 12978129887) (nat_lit 0) A10K2.u1279 from rfl, totK_node, atot1278, atot1279]
  decide +kernel

theorem arows1283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1283 = true := by
  rw [show A10K2.u1283 = KTree.node A10K2.u1281 (nat_lit 18373399) (nat_lit 2608182760) (nat_lit 0) A10K2.u1282 from rfl, allE_node, arows1281, irow1283, arows1282]
  all_goals rfl

theorem atot1283 : totK PA10K2 A10K2.u1283 = [0, 1369210211955, 5971036711615, 8219504336263, 3619177171883, 410077480046, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u1283 = KTree.node A10K2.u1281 (nat_lit 18373399) (nat_lit 2608182760) (nat_lit 0) A10K2.u1282 from rfl, totK_node, atot1281, atot1282]
  decide +kernel

theorem arows1287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1287 = true := by
  rw [show A10K2.u1287 = KTree.node A10K2.u1285 (nat_lit 18384940) (nat_lit 13025083326) (nat_lit 0) A10K2.u1286 from rfl, allE_node, arows1285, irow1287, arows1286]
  all_goals rfl

theorem atot1287 : totK PA10K2 A10K2.u1287 = [0, 0, 1361997545825, 5906690062786, 8092845110442, 3572929180942, 533064995855, 25239774317, 0, 0] := by
  rw [show A10K2.u1287 = KTree.node A10K2.u1285 (nat_lit 18384940) (nat_lit 13025083326) (nat_lit 0) A10K2.u1286 from rfl, totK_node, atot1285, atot1286]
  decide +kernel

theorem arows1290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1290 = true := by
  rw [show A10K2.u1290 = KTree.node A10K2.u1288 (nat_lit 18405718) (nat_lit 3670822459) (nat_lit 0) A10K2.u1289 from rfl, allE_node, arows1288, irow1290, arows1289]
  all_goals rfl

theorem atot1290 : totK PA10K2 A10K2.u1290 = [0, 190213598080, 1823387431598, 6056506314394, 7759808357204, 3241450405005, 406794894301, 10957026886, 0, 0] := by
  rw [show A10K2.u1290 = KTree.node A10K2.u1288 (nat_lit 18405718) (nat_lit 3670822459) (nat_lit 0) A10K2.u1289 from rfl, totK_node, atot1288, atot1289]
  decide +kernel

theorem arows1295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1295 = true := by
  rw [show A10K2.u1295 = KTree.node A10K2.u1293 (nat_lit 18440577) (nat_lit 10223008356) (nat_lit 0) A10K2.u1294 from rfl, allE_node, arows1293, irow1295, arows1294]
  all_goals rfl

theorem atot1295 : totK PA10K2 A10K2.u1295 = [0, 1198523436832, 5575237714068, 8509277868328, 4566373985743, 678846557300, 14899545677, 0, 0, 0] := by
  rw [show A10K2.u1295 = KTree.node A10K2.u1293 (nat_lit 18440577) (nat_lit 10223008356) (nat_lit 0) A10K2.u1294 from rfl, totK_node, atot1293, atot1294]
  decide +kernel

theorem arows1298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1298 = true := by
  rw [show A10K2.u1298 = KTree.node A10K2.u1296 (nat_lit 18460309) (nat_lit 5714453568) (nat_lit 0) A10K2.u1297 from rfl, allE_node, arows1296, irow1298, arows1297]
  all_goals rfl

theorem atot1298 : totK PA10K2 A10K2.u1298 = [0, 0, 1645518428832, 6614017491791, 8344065347196, 3394287276124, 385717013490, 8047840951, 0, 0] := by
  rw [show A10K2.u1298 = KTree.node A10K2.u1296 (nat_lit 18460309) (nat_lit 5714453568) (nat_lit 0) A10K2.u1297 from rfl, totK_node, atot1296, atot1297]
  decide +kernel

theorem arows1302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1302 = true := by
  rw [show A10K2.u1302 = KTree.node A10K2.u1300 (nat_lit 18550450) (nat_lit 14649064638) (nat_lit 0) A10K2.u1301 from rfl, allE_node, arows1300, irow1302, arows1301]
  all_goals rfl

theorem atot1302 : totK PA10K2 A10K2.u1302 = [0, 1105768476378, 4928684300080, 7680645589139, 4842878341422, 1165456603538, 81304987379, 0, 0, 0] := by
  rw [show A10K2.u1302 = KTree.node A10K2.u1300 (nat_lit 18550450) (nat_lit 14649064638) (nat_lit 0) A10K2.u1301 from rfl, totK_node, atot1300, atot1301]
  decide +kernel

theorem arows1305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1305 = true := by
  rw [show A10K2.u1305 = KTree.node A10K2.u1303 (nat_lit 18571811) (nat_lit 1942134352) (nat_lit 0) A10K2.u1304 from rfl, allE_node, arows1303, irow1305, arows1304]
  all_goals rfl

theorem atot1305 : totK PA10K2 A10K2.u1305 = [0, 1177977321196, 5379123776228, 8181980821119, 4559254648153, 737346807151, 20425520299, 0, 0, 0] := by
  rw [show A10K2.u1305 = KTree.node A10K2.u1303 (nat_lit 18571811) (nat_lit 1942134352) (nat_lit 0) A10K2.u1304 from rfl, totK_node, atot1303, atot1304]
  decide +kernel

theorem arows1311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1311 = true := by
  rw [show A10K2.u1311 = KTree.node A10K2.u1309 (nat_lit 18582024) (nat_lit 14167382902) (nat_lit 0) A10K2.u1310 from rfl, allE_node, arows1309, irow1311, arows1310]
  all_goals rfl

theorem atot1311 : totK PA10K2 A10K2.u1311 = [0, 0, 1487372169693, 6158715525360, 8063954407958, 3542438324275, 423285870820, 6904928264, 0, 0] := by
  rw [show A10K2.u1311 = KTree.node A10K2.u1309 (nat_lit 18582024) (nat_lit 14167382902) (nat_lit 0) A10K2.u1310 from rfl, totK_node, atot1309, atot1310]
  decide +kernel

theorem arows1314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1314 = true := by
  rw [show A10K2.u1314 = KTree.node A10K2.u1312 (nat_lit 18604088) (nat_lit 14859874300) (nat_lit 0) A10K2.u1313 from rfl, allE_node, arows1312, irow1314, arows1313]
  all_goals rfl

theorem atot1314 : totK PA10K2 A10K2.u1314 = [0, 0, 1343847593410, 6031203353543, 8408522424754, 3802270531284, 392724488595, 7047025452, 0, 0] := by
  rw [show A10K2.u1314 = KTree.node A10K2.u1312 (nat_lit 18604088) (nat_lit 14859874300) (nat_lit 0) A10K2.u1313 from rfl, totK_node, atot1312, atot1313]
  decide +kernel

theorem arows1318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1318 = true := by
  rw [show A10K2.u1318 = KTree.node A10K2.u1316 (nat_lit 18613138) (nat_lit 10299633310) (nat_lit 0) A10K2.u1317 from rfl, allE_node, arows1316, irow1318, arows1317]
  all_goals rfl

theorem atot1318 : totK PA10K2 A10K2.u1318 = [0, 0, 844183794776, 4213780595032, 7523306280624, 5409977156134, 1337742437225, 86443380410, 0, 0] := by
  rw [show A10K2.u1318 = KTree.node A10K2.u1316 (nat_lit 18613138) (nat_lit 10299633310) (nat_lit 0) A10K2.u1317 from rfl, totK_node, atot1316, atot1317]
  decide +kernel

theorem arows1321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1321 = true := by
  rw [show A10K2.u1321 = KTree.node A10K2.u1319 (nat_lit 18634848) (nat_lit 12991034545) (nat_lit 0) A10K2.u1320 from rfl, allE_node, arows1319, irow1321, arows1320]
  all_goals rfl

theorem atot1321 : totK PA10K2 A10K2.u1321 = [0, 0, 1369210211955, 5851146538385, 8075011197597, 3699017046549, 463037934721, 11152205789, 0, 0] := by
  rw [show A10K2.u1321 = KTree.node A10K2.u1319 (nat_lit 18634848) (nat_lit 12991034545) (nat_lit 0) A10K2.u1320 from rfl, totK_node, atot1319, atot1320]
  decide +kernel

theorem arows1326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1326 = true := by
  rw [show A10K2.u1326 = KTree.node A10K2.u1324 (nat_lit 18645541) (nat_lit 6835160537) (nat_lit 0) A10K2.u1325 from rfl, allE_node, arows1324, irow1326, arows1325]
  all_goals rfl

theorem atot1326 : totK PA10K2 A10K2.u1326 = [0, 0, 0, 1652629702008, 6585382916017, 8045906852105, 3010236525283, 339440665151, 7007974415, 0] := by
  rw [show A10K2.u1326 = KTree.node A10K2.u1324 (nat_lit 18645541) (nat_lit 6835160537) (nat_lit 0) A10K2.u1325 from rfl, totK_node, atot1324, atot1325]
  decide +kernel

theorem arows1329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1329 = true := by
  rw [show A10K2.u1329 = KTree.node A10K2.u1327 (nat_lit 18670994) (nat_lit 15341183866) (nat_lit 0) A10K2.u1328 from rfl, allE_node, arows1327, irow1329, arows1328]
  all_goals rfl

theorem atot1329 : totK PA10K2 A10K2.u1329 = [0, 0, 593578530300, 3501953561609, 7532797852741, 6398490263156, 1741417459599, 103174509101, 0, 0] := by
  rw [show A10K2.u1329 = KTree.node A10K2.u1327 (nat_lit 18670994) (nat_lit 15341183866) (nat_lit 0) A10K2.u1328 from rfl, totK_node, atot1327, atot1328]
  decide +kernel

theorem arows1333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1333 = true := by
  rw [show A10K2.u1333 = KTree.node A10K2.u1331 (nat_lit 18705599) (nat_lit 14180918075) (nat_lit 0) A10K2.u1332 from rfl, allE_node, arows1331, irow1333, arows1332]
  all_goals rfl

theorem atot1333 : totK PA10K2 A10K2.u1333 = [0, 0, 793160885870, 4348278942655, 8279569571206, 5893923255364, 1176602931157, 33098432694, 0, 0] := by
  rw [show A10K2.u1333 = KTree.node A10K2.u1331 (nat_lit 18705599) (nat_lit 14180918075) (nat_lit 0) A10K2.u1332 from rfl, totK_node, atot1331, atot1332]
  decide +kernel

theorem arows1336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1336 = true := by
  rw [show A10K2.u1336 = KTree.node A10K2.u1334 (nat_lit 18813489) (nat_lit 9945262219) (nat_lit 0) A10K2.u1335 from rfl, allE_node, arows1334, irow1336, arows1335]
  all_goals rfl

theorem atot1336 : totK PA10K2 A10K2.u1336 = [0, 0, 1409624687933, 5911696767737, 8004000389071, 3852862266072, 663229278987, 43676286325, 0, 0] := by
  rw [show A10K2.u1336 = KTree.node A10K2.u1334 (nat_lit 18813489) (nat_lit 9945262219) (nat_lit 0) A10K2.u1335 from rfl, totK_node, atot1334, atot1335]
  decide +kernel

theorem arows1343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1343 = true := by
  rw [show A10K2.u1343 = KTree.node A10K2.u1341 (nat_lit 18835335) (nat_lit 14414781266) (nat_lit 0) A10K2.u1342 from rfl, allE_node, arows1341, irow1343, arows1342]
  all_goals rfl

theorem atot1343 : totK PA10K2 A10K2.u1343 = [0, 0, 872630842479, 4661370482155, 8339069349498, 5294371585339, 831474838907, 21487697367, 0, 0] := by
  rw [show A10K2.u1343 = KTree.node A10K2.u1341 (nat_lit 18835335) (nat_lit 14414781266) (nat_lit 0) A10K2.u1342 from rfl, totK_node, atot1341, atot1342]
  decide +kernel

theorem arows1346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1346 = true := by
  rw [show A10K2.u1346 = KTree.node A10K2.u1344 (nat_lit 18845732) (nat_lit 11500670678) (nat_lit 0) A10K2.u1345 from rfl, allE_node, arows1344, irow1346, arows1345]
  all_goals rfl

theorem atot1346 : totK PA10K2 A10K2.u1346 = [0, 0, 0, 1628756948108, 6308803556060, 8088115248811, 3463137199214, 368538640554, 6318667960, 0] := by
  rw [show A10K2.u1346 = KTree.node A10K2.u1344 (nat_lit 18845732) (nat_lit 11500670678) (nat_lit 0) A10K2.u1345 from rfl, totK_node, atot1344, atot1345]
  decide +kernel

theorem arows1350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1350 = true := by
  rw [show A10K2.u1350 = KTree.node A10K2.u1348 (nat_lit 18871191) (nat_lit 14313742118) (nat_lit 0) A10K2.u1349 from rfl, allE_node, arows1348, irow1350, arows1349]
  all_goals rfl

theorem atot1350 : totK PA10K2 A10K2.u1350 = [0, 0, 650522015057, 2903985425289, 5813967563419, 6285129855711, 3405224880205, 670383622257, 35562304373, 0] := by
  rw [show A10K2.u1350 = KTree.node A10K2.u1348 (nat_lit 18871191) (nat_lit 14313742118) (nat_lit 0) A10K2.u1349 from rfl, totK_node, atot1348, atot1349]
  decide +kernel

theorem arows1353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1353 = true := by
  rw [show A10K2.u1353 = KTree.node A10K2.u1351 (nat_lit 18882034) (nat_lit 13055503498) (nat_lit 0) A10K2.u1352 from rfl, allE_node, arows1351, irow1353, arows1352]
  all_goals rfl

theorem atot1353 : totK PA10K2 A10K2.u1353 = [0, 0, 939450503551, 4922461097673, 8020490931546, 4372465033811, 684370145217, 30831673886, 0, 0] := by
  rw [show A10K2.u1353 = KTree.node A10K2.u1351 (nat_lit 18882034) (nat_lit 13055503498) (nat_lit 0) A10K2.u1352 from rfl, totK_node, atot1351, atot1352]
  decide +kernel

theorem arows1358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1358 = true := by
  rw [show A10K2.u1358 = KTree.node A10K2.u1356 (nat_lit 18902974) (nat_lit 16396326754) (nat_lit 0) A10K2.u1357 from rfl, allE_node, arows1356, irow1358, arows1357]
  all_goals rfl

theorem atot1358 : totK PA10K2 A10K2.u1358 = [0, 0, 777444773176, 4155902445346, 7820786464074, 5600602348398, 1249799745396, 63967737373, 0, 0] := by
  rw [show A10K2.u1358 = KTree.node A10K2.u1356 (nat_lit 18902974) (nat_lit 16396326754) (nat_lit 0) A10K2.u1357 from rfl, totK_node, atot1356, atot1357]
  decide +kernel

theorem arows1361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1361 = true := by
  rw [show A10K2.u1361 = KTree.node A10K2.u1359 (nat_lit 18913448) (nat_lit 8751241636) (nat_lit 0) A10K2.u1360 from rfl, allE_node, arows1359, irow1361, arows1360]
  all_goals rfl

theorem atot1361 : totK PA10K2 A10K2.u1361 = [0, 0, 0, 1263928825941, 5631988325258, 7721973519306, 3511560655332, 591979910942, 30650496230, 0] := by
  rw [show A10K2.u1361 = KTree.node A10K2.u1359 (nat_lit 18913448) (nat_lit 8751241636) (nat_lit 0) A10K2.u1360 from rfl, totK_node, atot1359, atot1360]
  decide +kernel

theorem arows1365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1365 = true := by
  rw [show A10K2.u1365 = KTree.node A10K2.u1363 (nat_lit 18935031) (nat_lit 14712644156) (nat_lit 0) A10K2.u1364 from rfl, allE_node, arows1363, irow1365, arows1364]
  all_goals rfl

theorem atot1365 : totK PA10K2 A10K2.u1365 = [0, 0, 798070509296, 3687549514179, 6570500411355, 5847987464794, 2222061317214, 256116959508, 5546304973, 0] := by
  rw [show A10K2.u1365 = KTree.node A10K2.u1363 (nat_lit 18935031) (nat_lit 14712644156) (nat_lit 0) A10K2.u1364 from rfl, totK_node, atot1363, atot1364]
  decide +kernel

theorem arows1368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1368 = true := by
  rw [show A10K2.u1368 = KTree.node A10K2.u1366 (nat_lit 19016040) (nat_lit 9482828573) (nat_lit 0) A10K2.u1367 from rfl, allE_node, arows1366, irow1368, arows1367]
  all_goals rfl

theorem atot1368 : totK PA10K2 A10K2.u1368 = [0, 0, 1000358553100, 4730643468989, 7584509842461, 4407079677536, 755145936415, 36865889447, 0, 0] := by
  rw [show A10K2.u1368 = KTree.node A10K2.u1366 (nat_lit 19016040) (nat_lit 9482828573) (nat_lit 0) A10K2.u1367 from rfl, totK_node, atot1366, atot1367]
  decide +kernel

theorem arows1374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1374 = true := by
  rw [show A10K2.u1374 = KTree.node A10K2.u1372 (nat_lit 19038977) (nat_lit 10372125357) (nat_lit 0) A10K2.u1373 from rfl, allE_node, arows1372, irow1374, arows1373]
  all_goals rfl

theorem atot1374 : totK PA10K2 A10K2.u1374 = [0, 0, 182725438514, 2909623685279, 7870521616198, 6353033621896, 1280629327681, 57019069441, 0, 0] := by
  rw [show A10K2.u1374 = KTree.node A10K2.u1372 (nat_lit 19038977) (nat_lit 10372125357) (nat_lit 0) A10K2.u1373 from rfl, totK_node, atot1372, atot1373]
  decide +kernel

theorem arows1377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1377 = true := by
  rw [show A10K2.u1377 = KTree.node A10K2.u1375 (nat_lit 19060946) (nat_lit 13734639332) (nat_lit 0) A10K2.u1376 from rfl, allE_node, arows1375, irow1377, arows1376]
  all_goals rfl

theorem atot1377 : totK PA10K2 A10K2.u1377 = [0, 0, 811506918617, 3628972990103, 6512273058191, 5726942687164, 1848032404313, 224172278478, 5976421810, 0] := by
  rw [show A10K2.u1377 = KTree.node A10K2.u1375 (nat_lit 19060946) (nat_lit 13734639332) (nat_lit 0) A10K2.u1376 from rfl, totK_node, atot1375, atot1376]
  decide +kernel

theorem arows1381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1381 = true := by
  rw [show A10K2.u1381 = KTree.node A10K2.u1379 (nat_lit 19083256) (nat_lit 12576069071) (nat_lit 0) A10K2.u1380 from rfl, allE_node, arows1379, irow1381, arows1380]
  all_goals rfl

theorem atot1381 : totK PA10K2 A10K2.u1381 = [0, 0, 1311715475833, 5673808412159, 8229877552269, 4231704087841, 683211971181, 30810868011, 0, 0] := by
  rw [show A10K2.u1381 = KTree.node A10K2.u1379 (nat_lit 19083256) (nat_lit 12576069071) (nat_lit 0) A10K2.u1380 from rfl, totK_node, atot1379, atot1380]
  decide +kernel

theorem arows1384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1384 = true := by
  rw [show A10K2.u1384 = KTree.node A10K2.u1382 (nat_lit 19104219) (nat_lit 3317526378) (nat_lit 8) A10K2.u1383 from rfl, allE_node, arows1382, irow1384, arows1383]
  all_goals rfl

theorem atot1384 : totK PA10K2 A10K2.u1384 = [0, 0, 0, 1742287979566, 6732147409742, 7950980852191, 3056945310191, 339697767266, 6904928264, 0] := by
  rw [show A10K2.u1384 = KTree.node A10K2.u1382 (nat_lit 19104219) (nat_lit 3317526378) (nat_lit 8) A10K2.u1383 from rfl, totK_node, atot1382, atot1383]
  decide +kernel

theorem arows1389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1389 = true := by
  rw [show A10K2.u1389 = KTree.node A10K2.u1387 (nat_lit 19131538) (nat_lit 15550823646) (nat_lit 0) A10K2.u1388 from rfl, allE_node, arows1387, irow1389, arows1388]
  all_goals rfl

theorem atot1389 : totK PA10K2 A10K2.u1389 = [0, 0, 0, 1522530464355, 6122574848406, 7905306615229, 3882204219694, 645850811500, 34570548376, 0] := by
  rw [show A10K2.u1389 = KTree.node A10K2.u1387 (nat_lit 19131538) (nat_lit 15550823646) (nat_lit 0) A10K2.u1388 from rfl, totK_node, atot1387, atot1388]
  decide +kernel

theorem arows1392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1392 = true := by
  rw [show A10K2.u1392 = KTree.node A10K2.u1390 (nat_lit 19141234) (nat_lit 5162868806) (nat_lit 0) A10K2.u1391 from rfl, allE_node, arows1390, irow1392, arows1391]
  all_goals rfl

theorem atot1392 : totK PA10K2 A10K2.u1392 = [0, 0, 0, 1262873778859, 5440022130047, 7773880828585, 3861927168743, 638642339226, 30831673886, 0] := by
  rw [show A10K2.u1392 = KTree.node A10K2.u1390 (nat_lit 19141234) (nat_lit 5162868806) (nat_lit 0) A10K2.u1391 from rfl, totK_node, atot1390, atot1391]
  decide +kernel

theorem arows1396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1396 = true := by
  rw [show A10K2.u1396 = KTree.node A10K2.u1394 (nat_lit 19162504) (nat_lit 13487654208) (nat_lit 0) A10K2.u1395 from rfl, allE_node, arows1394, irow1396, arows1395]
  all_goals rfl

theorem atot1396 : totK PA10K2 A10K2.u1396 = [0, 0, 0, 883603878394, 4820438867254, 8261775971997, 4543398840997, 684767339520, 18451199822, 0] := by
  rw [show A10K2.u1396 = KTree.node A10K2.u1394 (nat_lit 19162504) (nat_lit 13487654208) (nat_lit 0) A10K2.u1395 from rfl, totK_node, atot1394, atot1395]
  decide +kernel

theorem arows1399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1399 = true := by
  rw [show A10K2.u1399 = KTree.node A10K2.u1397 (nat_lit 19173782) (nat_lit 13224954799) (nat_lit 0) A10K2.u1398 from rfl, allE_node, arows1397, irow1399, arows1398]
  all_goals rfl

theorem atot1399 : totK PA10K2 A10K2.u1399 = [0, 0, 0, 0, 1349402491274, 5533697086480, 7422376371489, 3619115125391, 628135404284, 30605747850] := by
  rw [show A10K2.u1399 = KTree.node A10K2.u1397 (nat_lit 19173782) (nat_lit 13224954799) (nat_lit 0) A10K2.u1398 from rfl, totK_node, atot1397, atot1398]
  decide +kernel

theorem arows1407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1407 = true := by
  rw [show A10K2.u1407 = KTree.node A10K2.u1405 (nat_lit 19195070) (nat_lit 14687829832) (nat_lit 0) A10K2.u1406 from rfl, allE_node, arows1405, irow1407, arows1406]
  all_goals rfl

theorem atot1407 : totK PA10K2 A10K2.u1407 = [0, 0, 0, 794671563991, 3576589607203, 6504494456564, 5666652883803, 2016796429286, 231488854593, 5528811039] := by
  rw [show A10K2.u1407 = KTree.node A10K2.u1405 (nat_lit 19195070) (nat_lit 14687829832) (nat_lit 0) A10K2.u1406 from rfl, totK_node, atot1405, atot1406]
  decide +kernel

theorem arows1410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1410 = true := by
  rw [show A10K2.u1410 = KTree.node A10K2.u1408 (nat_lit 19277987) (nat_lit 10499862237) (nat_lit 0) A10K2.u1409 from rfl, allE_node, arows1408, irow1410, arows1409]
  all_goals rfl

theorem atot1410 : totK PA10K2 A10K2.u1410 = [0, 0, 0, 927178124941, 4741764101271, 7773092016034, 4195529324499, 733088053082, 36487828629, 0] := by
  rw [show A10K2.u1410 = KTree.node A10K2.u1408 (nat_lit 19277987) (nat_lit 10499862237) (nat_lit 0) A10K2.u1409 from rfl, totK_node, atot1408, atot1409]
  decide +kernel

theorem arows1414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1414 = true := by
  rw [show A10K2.u1414 = KTree.node A10K2.u1412 (nat_lit 19300908) (nat_lit 11662701168) (nat_lit 0) A10K2.u1413 from rfl, allE_node, arows1412, irow1414, arows1413]
  all_goals rfl

theorem atot1414 : totK PA10K2 A10K2.u1414 = [0, 0, 0, 257913039921, 3313015876811, 8048126225229, 5714534211264, 1109822530057, 50767597675, 0] := by
  rw [show A10K2.u1414 = KTree.node A10K2.u1412 (nat_lit 19300908) (nat_lit 11662701168) (nat_lit 0) A10K2.u1413 from rfl, totK_node, atot1412, atot1413]
  decide +kernel

theorem arows1417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1417 = true := by
  rw [show A10K2.u1417 = KTree.node A10K2.u1415 (nat_lit 19323657) (nat_lit 8147714579) (nat_lit 0) A10K2.u1416 from rfl, allE_node, arows1415, irow1417, arows1416]
  all_goals rfl

theorem atot1417 : totK PA10K2 A10K2.u1417 = [0, 0, 0, 808333325195, 3739028945660, 6709664983997, 5432639117600, 1749648112140, 222427489243, 5676195732] := by
  rw [show A10K2.u1417 = KTree.node A10K2.u1415 (nat_lit 19323657) (nat_lit 8147714579) (nat_lit 0) A10K2.u1416 from rfl, totK_node, atot1415, atot1416]
  decide +kernel

theorem arows1422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1422 = true := by
  rw [show A10K2.u1422 = KTree.node A10K2.u1420 (nat_lit 19358882) (nat_lit 10528994882) (nat_lit 0) A10K2.u1421 from rfl, allE_node, arows1420, irow1422, arows1421]
  all_goals rfl

theorem atot1422 : totK PA10K2 A10K2.u1422 = [0, 0, 0, 1310490722185, 5766939616638, 8227529845814, 4265185633518, 617120732564, 21795074124, 0] := by
  rw [show A10K2.u1422 = KTree.node A10K2.u1420 (nat_lit 19358882) (nat_lit 10528994882) (nat_lit 0) A10K2.u1421 from rfl, totK_node, atot1420, atot1421]
  decide +kernel

theorem arows1425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1425 = true := by
  rw [show A10K2.u1425 = KTree.node A10K2.u1423 (nat_lit 19927116) (nat_lit 10725755786) (nat_lit 0) A10K2.u1424 from rfl, allE_node, arows1423, irow1425, arows1424]
  all_goals rfl

theorem atot1425 : totK PA10K2 A10K2.u1425 = [0, 0, 1228511409809, 5149298357534, 7334064455715, 3992141323767, 1110062975388, 296621305298, 28650013862, 0] := by
  rw [show A10K2.u1425 = KTree.node A10K2.u1423 (nat_lit 19927116) (nat_lit 10725755786) (nat_lit 0) A10K2.u1424 from rfl, totK_node, atot1423, atot1424]
  decide +kernel

theorem arows1429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1429 = true := by
  rw [show A10K2.u1429 = KTree.node A10K2.u1427 (nat_lit 19947639) (nat_lit 14469999615) (nat_lit 0) A10K2.u1428 from rfl, allE_node, arows1427, irow1429, arows1428]
  all_goals rfl

theorem atot1429 : totK PA10K2 A10K2.u1429 = [0, 0, 952688695273, 4925862144122, 8187553847252, 4646898597134, 718390079269, 19100662535, 0, 0] := by
  rw [show A10K2.u1429 = KTree.node A10K2.u1427 (nat_lit 19947639) (nat_lit 14469999615) (nat_lit 0) A10K2.u1428 from rfl, totK_node, atot1427, atot1428]
  decide +kernel

theorem arows1432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1432 = true := by
  rw [show A10K2.u1432 = KTree.node A10K2.u1430 (nat_lit 19960199) (nat_lit 14213163043) (nat_lit 0) A10K2.u1431 from rfl, allE_node, arows1430, irow1432, arows1431]
  all_goals rfl

theorem atot1432 : totK PA10K2 A10K2.u1432 = [0, 0, 0, 1297561586026, 5590679731038, 7710375384402, 3650231778971, 629493104229, 30650496230, 0] := by
  rw [show A10K2.u1432 = KTree.node A10K2.u1430 (nat_lit 19960199) (nat_lit 14213163043) (nat_lit 0) A10K2.u1431 from rfl, totK_node, atot1430, atot1431]
  decide +kernel

theorem arows1438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1438 = true := by
  rw [show A10K2.u1438 = KTree.node A10K2.u1436 (nat_lit 19981064) (nat_lit 13953022228) (nat_lit 0) A10K2.u1437 from rfl, allE_node, arows1436, irow1438, arows1437]
  all_goals rfl

theorem atot1438 : totK PA10K2 A10K2.u1438 = [0, 0, 560899012013, 3210330383452, 6657612983936, 6272708624849, 2265415412129, 254868438694, 5546304973, 0] := by
  rw [show A10K2.u1438 = KTree.node A10K2.u1436 (nat_lit 19981064) (nat_lit 13953022228) (nat_lit 0) A10K2.u1437 from rfl, totK_node, atot1436, atot1437]
  decide +kernel

theorem arows1441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1441 = true := by
  rw [show A10K2.u1441 = KTree.node A10K2.u1439 (nat_lit 20007750) (nat_lit 6496273987) (nat_lit 0) A10K2.u1440 from rfl, allE_node, arows1439, irow1441, arows1440]
  all_goals rfl

theorem atot1441 : totK PA10K2 A10K2.u1441 = [0, 0, 738658298461, 4395849694840, 8183220060036, 4796058701733, 727949101530, 18433134592, 0, 0] := by
  rw [show A10K2.u1441 = KTree.node A10K2.u1439 (nat_lit 20007750) (nat_lit 6496273987) (nat_lit 0) A10K2.u1440 from rfl, totK_node, atot1439, atot1440]
  decide +kernel

theorem arows1445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1445 = true := by
  rw [show A10K2.u1445 = KTree.node A10K2.u1443 (nat_lit 20044580) (nat_lit 14092073173) (nat_lit 0) A10K2.u1444 from rfl, allE_node, arows1443, irow1445, arows1444]
  all_goals rfl

theorem atot1445 : totK PA10K2 A10K2.u1445 = [0, 0, 762134139439, 3653067142078, 6882367657513, 5782522242372, 1759765437563, 152091523344, 6121173289, 0] := by
  rw [show A10K2.u1445 = KTree.node A10K2.u1443 (nat_lit 20044580) (nat_lit 14092073173) (nat_lit 0) A10K2.u1444 from rfl, totK_node, atot1443, atot1444]
  decide +kernel

theorem arows1448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1448 = true := by
  rw [show A10K2.u1448 = KTree.node A10K2.u1446 (nat_lit 20065506) (nat_lit 14274607010) (nat_lit 0) A10K2.u1447 from rfl, allE_node, arows1446, irow1448, arows1447]
  all_goals rfl

theorem atot1448 : totK PA10K2 A10K2.u1448 = [0, 0, 1097531576858, 4890436005308, 7507869355353, 4339509405231, 812240092060, 42259512619, 0, 0] := by
  rw [show A10K2.u1448 = KTree.node A10K2.u1446 (nat_lit 20065506) (nat_lit 14274607010) (nat_lit 0) A10K2.u1447 from rfl, totK_node, atot1446, atot1447]
  decide +kernel

theorem arows1453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1453 = true := by
  rw [show A10K2.u1453 = KTree.node A10K2.u1451 (nat_lit 20086862) (nat_lit 10856236912) (nat_lit 0) A10K2.u1452 from rfl, allE_node, arows1451, irow1453, arows1452]
  all_goals rfl

theorem atot1453 : totK PA10K2 A10K2.u1453 = [0, 0, 308781236982, 3247164972641, 7990737058659, 6069478361066, 1224899800890, 50664460339, 0, 0] := by
  rw [show A10K2.u1453 = KTree.node A10K2.u1451 (nat_lit 20086862) (nat_lit 10856236912) (nat_lit 0) A10K2.u1452 from rfl, totK_node, atot1451, atot1452]
  decide +kernel

theorem arows1456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1456 = true := by
  rw [show A10K2.u1456 = KTree.node A10K2.u1454 (nat_lit 20106049) (nat_lit 8760375159) (nat_lit 0) A10K2.u1455 from rfl, allE_node, arows1454, irow1456, arows1455]
  all_goals rfl

theorem atot1456 : totK PA10K2 A10K2.u1456 = [0, 0, 0, 1571482318054, 6431819484511, 7673053461053, 2602536100097, 277920431475, 6354482628, 0] := by
  rw [show A10K2.u1456 = KTree.node A10K2.u1454 (nat_lit 20106049) (nat_lit 8760375159) (nat_lit 0) A10K2.u1455 from rfl, totK_node, atot1454, atot1455]
  decide +kernel

theorem arows1460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1460 = true := by
  rw [show A10K2.u1460 = KTree.node A10K2.u1458 (nat_lit 20192498) (nat_lit 8457700859) (nat_lit 0) A10K2.u1459 from rfl, allE_node, arows1458, irow1460, arows1459]
  all_goals rfl

theorem atot1460 : totK PA10K2 A10K2.u1460 = [0, 0, 0, 1008673779874, 5110212176148, 8039094166428, 4014542455038, 646239206434, 30818366867, 0] := by
  rw [show A10K2.u1460 = KTree.node A10K2.u1458 (nat_lit 20192498) (nat_lit 8457700859) (nat_lit 0) A10K2.u1459 from rfl, totK_node, atot1458, atot1459]
  decide +kernel

theorem arows1463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1463 = true := by
  rw [show A10K2.u1463 = KTree.node A10K2.u1461 (nat_lit 20214144) (nat_lit 15309605149) (nat_lit 0) A10K2.u1462 from rfl, allE_node, arows1461, irow1463, arows1462]
  all_goals rfl

theorem atot1463 : totK PA10K2 A10K2.u1463 = [0, 0, 0, 1391180431590, 5894582195764, 7946865650972, 3603217664145, 503152609696, 13207830636, 0] := by
  rw [show A10K2.u1463 = KTree.node A10K2.u1461 (nat_lit 20214144) (nat_lit 15309605149) (nat_lit 0) A10K2.u1462 from rfl, totK_node, atot1461, atot1462]
  decide +kernel

theorem arows1470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1470 = true := by
  rw [show A10K2.u1470 = KTree.node A10K2.u1468 (nat_lit 20316222) (nat_lit 14150203385) (nat_lit 0) A10K2.u1469 from rfl, allE_node, arows1468, irow1470, arows1469]
  all_goals rfl

theorem atot1470 : totK PA10K2 A10K2.u1470 = [0, 0, 0, 1252178461080, 5668664884089, 7896632197082, 3430976337897, 493628334634, 30968873281, 0] := by
  rw [show A10K2.u1470 = KTree.node A10K2.u1468 (nat_lit 20316222) (nat_lit 14150203385) (nat_lit 0) A10K2.u1469 from rfl, totK_node, atot1468, atot1469]
  decide +kernel

theorem arows1473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1473 = true := by
  rw [show A10K2.u1473 = KTree.node A10K2.u1471 (nat_lit 20330528) (nat_lit 13214364479) (nat_lit 0) A10K2.u1472 from rfl, allE_node, arows1471, irow1473, arows1472]
  all_goals rfl

theorem atot1473 : totK PA10K2 A10K2.u1473 = [0, 0, 0, 1402066758156, 5900176190597, 7751718424458, 3164484641003, 372805181141, 11494708454, 0] := by
  rw [show A10K2.u1473 = KTree.node A10K2.u1471 (nat_lit 20330528) (nat_lit 13214364479) (nat_lit 0) A10K2.u1472 from rfl, totK_node, atot1471, atot1472]
  decide +kernel

theorem arows1477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1477 = true := by
  rw [show A10K2.u1477 = KTree.node A10K2.u1475 (nat_lit 20351194) (nat_lit 10128153703) (nat_lit 0) A10K2.u1476 from rfl, allE_node, arows1475, irow1477, arows1476]
  all_goals rfl

theorem atot1477 : totK PA10K2 A10K2.u1477 = [0, 0, 0, 0, 2700938604592, 8229045180003, 6135983521046, 1206829028169, 68557712875, 0] := by
  rw [show A10K2.u1477 = KTree.node A10K2.u1475 (nat_lit 20351194) (nat_lit 10128153703) (nat_lit 0) A10K2.u1476 from rfl, totK_node, atot1475, atot1476]
  decide +kernel

theorem arows1480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1480 = true := by
  rw [show A10K2.u1480 = KTree.node A10K2.u1478 (nat_lit 20447666) (nat_lit 11559200774) (nat_lit 0) A10K2.u1479 from rfl, allE_node, arows1478, irow1480, arows1479]
  all_goals rfl

theorem atot1480 : totK PA10K2 A10K2.u1480 = [0, 0, 842261825863, 3390952045022, 4752871272962, 4349049165328, 3746021560066, 1500273296503, 199159747666, 5976421810] := by
  rw [show A10K2.u1480 = KTree.node A10K2.u1478 (nat_lit 20447666) (nat_lit 11559200774) (nat_lit 0) A10K2.u1479 from rfl, totK_node, atot1478, atot1479]
  decide +kernel

theorem arows1485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1485 = true := by
  rw [show A10K2.u1485 = KTree.node A10K2.u1483 (nat_lit 20467777) (nat_lit 10353966038) (nat_lit 0) A10K2.u1484 from rfl, allE_node, arows1483, irow1485, arows1484]
  all_goals rfl

theorem atot1485 : totK PA10K2 A10K2.u1485 = [0, 0, 1367303922230, 5723224677730, 7883465811956, 3761496885263, 537406333889, 16737332881, 0, 0] := by
  rw [show A10K2.u1485 = KTree.node A10K2.u1483 (nat_lit 20467777) (nat_lit 10353966038) (nat_lit 0) A10K2.u1484 from rfl, totK_node, atot1483, atot1484]
  decide +kernel

theorem arows1488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1488 = true := by
  rw [show A10K2.u1488 = KTree.node A10K2.u1486 (nat_lit 20480114) (nat_lit 9386453866) (nat_lit 0) A10K2.u1487 from rfl, allE_node, arows1486, irow1488, arows1487]
  all_goals rfl

theorem atot1488 : totK PA10K2 A10K2.u1488 = [0, 0, 0, 1988175351297, 7222170467374, 7731699077016, 2544581629457, 300742379932, 14945844243, 0] := by
  rw [show A10K2.u1488 = KTree.node A10K2.u1486 (nat_lit 20480114) (nat_lit 9386453866) (nat_lit 0) A10K2.u1487 from rfl, totK_node, atot1486, atot1487]
  decide +kernel

theorem arows1492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1492 = true := by
  rw [show A10K2.u1492 = KTree.node A10K2.u1490 (nat_lit 20505018) (nat_lit 12632304876) (nat_lit 0) A10K2.u1491 from rfl, allE_node, arows1490, irow1492, arows1491]
  all_goals rfl

theorem atot1492 : totK PA10K2 A10K2.u1492 = [0, 0, 509119267445, 2947123495463, 6869242948450, 6796347034505, 2390522871409, 285979667840, 5179162207, 0] := by
  rw [show A10K2.u1492 = KTree.node A10K2.u1490 (nat_lit 20505018) (nat_lit 12632304876) (nat_lit 0) A10K2.u1491 from rfl, totK_node, atot1490, atot1491]
  decide +kernel

theorem arows1495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1495 = true := by
  rw [show A10K2.u1495 = KTree.node A10K2.u1493 (nat_lit 20541497) (nat_lit 7295847300) (nat_lit 0) A10K2.u1494 from rfl, allE_node, arows1493, irow1495, arows1494]
  all_goals rfl

theorem atot1495 : totK PA10K2 A10K2.u1495 = [0, 0, 1179657796222, 5306088517759, 8045673857832, 4804339426656, 1069354177407, 62712130859, 0, 0] := by
  rw [show A10K2.u1495 = KTree.node A10K2.u1493 (nat_lit 20541497) (nat_lit 7295847300) (nat_lit 0) A10K2.u1494 from rfl, totK_node, atot1493, atot1494]
  decide +kernel

theorem arows1501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1501 = true := by
  rw [show A10K2.u1501 = KTree.node A10K2.u1499 (nat_lit 20651078) (nat_lit 15137448907) (nat_lit 0) A10K2.u1500 from rfl, allE_node, arows1499, irow1501, arows1500]
  all_goals rfl

theorem atot1501 : totK PA10K2 A10K2.u1501 = [0, 0, 1108332851557, 5286764363899, 8323678949766, 4656045715898, 730235011694, 28077775223, 0, 0] := by
  rw [show A10K2.u1501 = KTree.node A10K2.u1499 (nat_lit 20651078) (nat_lit 15137448907) (nat_lit 0) A10K2.u1500 from rfl, totK_node, atot1499, atot1500]
  decide +kernel

theorem arows1504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1504 = true := by
  rw [show A10K2.u1504 = KTree.node A10K2.u1502 (nat_lit 20672448) (nat_lit 14627760404) (nat_lit 0) A10K2.u1503 from rfl, allE_node, arows1502, irow1504, arows1503]
  all_goals rfl

theorem atot1504 : totK PA10K2 A10K2.u1504 = [0, 0, 873613144665, 4552236506324, 8013959459677, 5357217033984, 1144408167018, 62996513375, 0, 0] := by
  rw [show A10K2.u1504 = KTree.node A10K2.u1502 (nat_lit 20672448) (nat_lit 14627760404) (nat_lit 0) A10K2.u1503 from rfl, totK_node, atot1502, atot1503]
  decide +kernel

theorem arows1508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1508 = true := by
  rw [show A10K2.u1508 = KTree.node A10K2.u1506 (nat_lit 20683820) (nat_lit 8472796316) (nat_lit 0) A10K2.u1507 from rfl, allE_node, arows1506, irow1508, arows1507]
  all_goals rfl

theorem atot1508 : totK PA10K2 A10K2.u1508 = [0, 0, 0, 1684428975636, 6705873852319, 8111374932282, 3248490804054, 383394300050, 6904928264, 0] := by
  rw [show A10K2.u1508 = KTree.node A10K2.u1506 (nat_lit 20683820) (nat_lit 8472796316) (nat_lit 0) A10K2.u1507 from rfl, totK_node, atot1506, atot1507]
  decide +kernel

theorem arows1511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1511 = true := by
  rw [show A10K2.u1511 = KTree.node A10K2.u1509 (nat_lit 25165824) (nat_lit 15792662511) (nat_lit 0) A10K2.u1510 from rfl, allE_node, arows1509, irow1511, arows1510]
  all_goals rfl

theorem atot1511 : totK PA10K2 A10K2.u1511 = [0, 857716201818, 3393588752070, 4354510555841, 3495917760175, 4221648304363, 2876961366724, 601701167053, 35608018656, 0] := by
  rw [show A10K2.u1511 = KTree.node A10K2.u1509 (nat_lit 25165824) (nat_lit 15792662511) (nat_lit 0) A10K2.u1510 from rfl, totK_node, atot1509, atot1510]
  decide +kernel

theorem arows1516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1516 = true := by
  rw [show A10K2.u1516 = KTree.node A10K2.u1514 (nat_lit 25183966) (nat_lit 4531957829) (nat_lit 0) A10K2.u1515 from rfl, allE_node, arows1514, irow1516, arows1515]
  all_goals rfl

theorem atot1516 : totK PA10K2 A10K2.u1516 = [0, 1039933805937, 4750376932029, 7620728876777, 4622270563300, 850469906557, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u1516 = KTree.node A10K2.u1514 (nat_lit 25183966) (nat_lit 4531957829) (nat_lit 0) A10K2.u1515 from rfl, totK_node, atot1514, atot1515]
  decide +kernel

theorem arows1519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1519 = true := by
  rw [show A10K2.u1519 = KTree.node A10K2.u1517 (nat_lit 25197972) (nat_lit 3666918464) (nat_lit 0) A10K2.u1518 from rfl, allE_node, arows1517, irow1519, arows1518]
  all_goals rfl

theorem atot1519 : totK PA10K2 A10K2.u1519 = [0, 395296435550, 3370803106576, 8036488596380, 6673804644393, 1631627201831, 86189949824, 0, 0, 0] := by
  rw [show A10K2.u1519 = KTree.node A10K2.u1517 (nat_lit 25197972) (nat_lit 3666918464) (nat_lit 0) A10K2.u1518 from rfl, totK_node, atot1517, atot1518]
  decide +kernel

theorem arows1523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1523 = true := by
  rw [show A10K2.u1523 = KTree.node A10K2.u1521 (nat_lit 25215850) (nat_lit 5464049142) (nat_lit 0) A10K2.u1522 from rfl, allE_node, arows1521, irow1523, arows1522]
  all_goals rfl

theorem atot1523 : totK PA10K2 A10K2.u1523 = [0, 0, 853100666974, 4585101198150, 7913729685643, 4465492492868, 773699802715, 36196801203, 0, 0] := by
  rw [show A10K2.u1523 = KTree.node A10K2.u1521 (nat_lit 25215850) (nat_lit 5464049142) (nat_lit 0) A10K2.u1522 from rfl, totK_node, atot1521, atot1522]
  decide +kernel

theorem arows1526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1526 = true := by
  rw [show A10K2.u1526 = KTree.node A10K2.u1524 (nat_lit 25299154) (nat_lit 13751151660) (nat_lit 0) A10K2.u1525 from rfl, allE_node, arows1524, irow1526, arows1525]
  all_goals rfl

theorem atot1526 : totK PA10K2 A10K2.u1526 = [0, 786880231059, 4133608314013, 7702177726908, 5675231303721, 1442900356687, 93460675711, 0, 0, 0] := by
  rw [show A10K2.u1526 = KTree.node A10K2.u1524 (nat_lit 25299154) (nat_lit 13751151660) (nat_lit 0) A10K2.u1525 from rfl, totK_node, atot1524, atot1525]
  decide +kernel

theorem arows1536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1536 = true := by
  rw [show A10K2.u1536 = KTree.node A10K2.u1534 (nat_lit 25311750) (nat_lit 9855463918) (nat_lit 0) A10K2.u1535 from rfl, allE_node, arows1534, irow1536, arows1535]
  all_goals rfl

theorem atot1536 : totK PA10K2 A10K2.u1536 = [0, 1328023409878, 5584552115193, 7530421857366, 3675872176465, 604349514617, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1536 = KTree.node A10K2.u1534 (nat_lit 25311750) (nat_lit 9855463918) (nat_lit 0) A10K2.u1535 from rfl, totK_node, atot1534, atot1535]
  decide +kernel

theorem arows1539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1539 = true := by
  rw [show A10K2.u1539 = KTree.node A10K2.u1537 (nat_lit 25332384) (nat_lit 8723241862) (nat_lit 0) A10K2.u1538 from rfl, allE_node, arows1537, irow1539, arows1538]
  all_goals rfl

theorem atot1539 : totK PA10K2 A10K2.u1539 = [0, 0, 2237430795111, 7714665269952, 7244283059761, 1733427467800, 96922413434, 0, 0, 0] := by
  rw [show A10K2.u1539 = KTree.node A10K2.u1537 (nat_lit 25332384) (nat_lit 8723241862) (nat_lit 0) A10K2.u1538 from rfl, totK_node, atot1537, atot1538]
  decide +kernel

theorem arows1543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1543 = true := by
  rw [show A10K2.u1543 = KTree.node A10K2.u1541 (nat_lit 25352532) (nat_lit 13140071320) (nat_lit 0) A10K2.u1542 from rfl, allE_node, arows1541, irow1543, arows1542]
  all_goals rfl

theorem atot1543 : totK PA10K2 A10K2.u1543 = [0, 808480932972, 3630883131525, 6396163492945, 5754272358273, 2179287412917, 296726858193, 6354482628, 0, 0] := by
  rw [show A10K2.u1543 = KTree.node A10K2.u1541 (nat_lit 25352532) (nat_lit 13140071320) (nat_lit 0) A10K2.u1542 from rfl, totK_node, atot1541, atot1542]
  decide +kernel

theorem arows1546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1546 = true := by
  rw [show A10K2.u1546 = KTree.node A10K2.u1544 (nat_lit 25388934) (nat_lit 15739099365) (nat_lit 0) A10K2.u1545 from rfl, allE_node, arows1544, irow1546, arows1545]
  all_goals rfl

theorem atot1546 : totK PA10K2 A10K2.u1546 = [0, 797258379978, 4379908573122, 8290568433551, 5656421177566, 1105862842153, 43557047918, 0, 0, 0] := by
  rw [show A10K2.u1546 = KTree.node A10K2.u1544 (nat_lit 25388934) (nat_lit 15739099365) (nat_lit 0) A10K2.u1545 from rfl, totK_node, atot1544, atot1545]
  decide +kernel

theorem arows1551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1551 = true := by
  rw [show A10K2.u1551 = KTree.node A10K2.u1549 (nat_lit 25399762) (nat_lit 10145771367) (nat_lit 0) A10K2.u1550 from rfl, allE_node, arows1549, irow1551, arows1550]
  all_goals rfl

theorem atot1551 : totK PA10K2 A10K2.u1551 = [0, 0, 1604792187001, 6394803769318, 8215116121885, 3491324795181, 394644933544, 6904928264, 0, 0] := by
  rw [show A10K2.u1551 = KTree.node A10K2.u1549 (nat_lit 25399762) (nat_lit 10145771367) (nat_lit 0) A10K2.u1550 from rfl, totK_node, atot1549, atot1550]
  decide +kernel

theorem arows1554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1554 = true := by
  rw [show A10K2.u1554 = KTree.node A10K2.u1552 (nat_lit 25428480) (nat_lit 15717770038) (nat_lit 0) A10K2.u1553 from rfl, allE_node, arows1552, irow1554, arows1553]
  all_goals rfl

theorem atot1554 : totK PA10K2 A10K2.u1554 = [0, 0, 855172175669, 4538014533117, 7991683024342, 5201361635821, 1062733419427, 60979199649, 0, 0] := by
  rw [show A10K2.u1554 = KTree.node A10K2.u1552 (nat_lit 25428480) (nat_lit 15717770038) (nat_lit 0) A10K2.u1553 from rfl, totK_node, atot1552, atot1553]
  decide +kernel

theorem arows1558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1558 = true := by
  rw [show A10K2.u1558 = KTree.node A10K2.u1556 (nat_lit 25446740) (nat_lit 13140071320) (nat_lit 0) A10K2.u1557 from rfl, allE_node, arows1556, irow1558, arows1557]
  all_goals rfl

theorem atot1558 : totK PA10K2 A10K2.u1558 = [0, 0, 1140194939132, 5421276796473, 8105411274200, 3838981884504, 469515660297, 11165512808, 0, 0] := by
  rw [show A10K2.u1558 = KTree.node A10K2.u1556 (nat_lit 25446740) (nat_lit 13140071320) (nat_lit 0) A10K2.u1557 from rfl, totK_node, atot1556, atot1557]
  decide +kernel

theorem arows1561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1561 = true := by
  rw [show A10K2.u1561 = KTree.node A10K2.u1559 (nat_lit 25461025) (nat_lit 9918507036) (nat_lit 0) A10K2.u1560 from rfl, allE_node, arows1559, irow1561, arows1560]
  all_goals rfl

theorem atot1561 : totK PA10K2 A10K2.u1561 = [0, 0, 293418347279, 2619877360552, 7074150756747, 7016488747058, 2326009918608, 319764392290, 20060612110, 0] := by
  rw [show A10K2.u1561 = KTree.node A10K2.u1559 (nat_lit 25461025) (nat_lit 9918507036) (nat_lit 0) A10K2.u1560 from rfl, totK_node, atot1559, atot1560]
  decide +kernel

theorem arows1567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1567 = true := by
  rw [show A10K2.u1567 = KTree.node A10K2.u1565 (nat_lit 25479453) (nat_lit 6440772232) (nat_lit 0) A10K2.u1566 from rfl, allE_node, arows1565, irow1567, arows1566]
  all_goals rfl

theorem atot1567 : totK PA10K2 A10K2.u1567 = [0, 0, 0, 1266081450648, 5574573271202, 7687787809988, 3519790113178, 528723132282, 16073946779, 0] := by
  rw [show A10K2.u1567 = KTree.node A10K2.u1565 (nat_lit 25479453) (nat_lit 6440772232) (nat_lit 0) A10K2.u1566 from rfl, totK_node, atot1565, atot1566]
  decide +kernel

theorem arows1570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1570 = true := by
  rw [show A10K2.u1570 = KTree.node A10K2.u1568 (nat_lit 25563137) (nat_lit 10630474206) (nat_lit 0) A10K2.u1569 from rfl, allE_node, arows1568, irow1570, arows1569]
  all_goals rfl

theorem atot1570 : totK PA10K2 A10K2.u1570 = [0, 0, 1196895285670, 5067006571178, 7625589907699, 4514173079526, 956489874550, 59842360860, 0, 0] := by
  rw [show A10K2.u1570 = KTree.node A10K2.u1568 (nat_lit 25563137) (nat_lit 10630474206) (nat_lit 0) A10K2.u1569 from rfl, totK_node, atot1568, atot1569]
  decide +kernel

theorem arows1574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1574 = true := by
  rw [show A10K2.u1574 = KTree.node A10K2.u1572 (nat_lit 25577122) (nat_lit 14360341732) (nat_lit 0) A10K2.u1573 from rfl, allE_node, arows1572, irow1574, arows1573]
  all_goals rfl

theorem atot1574 : totK PA10K2 A10K2.u1574 = [0, 0, 916882235497, 4981188548678, 8069552655669, 3988042924793, 537013518268, 12388698189, 0, 0] := by
  rw [show A10K2.u1574 = KTree.node A10K2.u1572 (nat_lit 25577122) (nat_lit 14360341732) (nat_lit 0) A10K2.u1573 from rfl, totK_node, atot1572, atot1573]
  decide +kernel

theorem arows1577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1577 = true := by
  rw [show A10K2.u1577 = KTree.node A10K2.u1575 (nat_lit 25602572) (nat_lit 11590646080) (nat_lit 0) A10K2.u1576 from rfl, allE_node, arows1575, irow1577, arows1576]
  all_goals rfl

theorem atot1577 : totK PA10K2 A10K2.u1577 = [0, 0, 0, 1980004247281, 7384328228011, 7398013791042, 1867216512444, 107556580210, 0, 0] := by
  rw [show A10K2.u1577 = KTree.node A10K2.u1575 (nat_lit 25602572) (nat_lit 11590646080) (nat_lit 0) A10K2.u1576 from rfl, totK_node, atot1575, atot1576]
  decide +kernel

theorem arows1582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1582 = true := by
  rw [show A10K2.u1582 = KTree.node A10K2.u1580 (nat_lit 25628192) (nat_lit 13996603243) (nat_lit 0) A10K2.u1581 from rfl, allE_node, arows1580, irow1582, arows1581]
  all_goals rfl

theorem atot1582 : totK PA10K2 A10K2.u1582 = [0, 0, 1173447475401, 4904795992061, 7269331048902, 4601163765530, 1419285550232, 185475499233, 5676195732, 0] := by
  rw [show A10K2.u1582 = KTree.node A10K2.u1580 (nat_lit 25628192) (nat_lit 13996603243) (nat_lit 0) A10K2.u1581 from rfl, totK_node, atot1580, atot1581]
  decide +kernel

theorem arows1585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1585 = true := by
  rw [show A10K2.u1585 = KTree.node A10K2.u1583 (nat_lit 25656772) (nat_lit 6537550957) (nat_lit 0) A10K2.u1584 from rfl, allE_node, arows1583, irow1585, arows1584]
  all_goals rfl

theorem atot1585 : totK PA10K2 A10K2.u1585 = [0, 843291061595, 3517274638175, 5847440466120, 5777246116988, 3411768518592, 725987504617, 36540832150, 0, 0] := by
  rw [show A10K2.u1585 = KTree.node A10K2.u1583 (nat_lit 25656772) (nat_lit 6537550957) (nat_lit 0) A10K2.u1584 from rfl, totK_node, atot1583, atot1584]
  decide +kernel

theorem arows1589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1589 = true := by
  rw [show A10K2.u1589 = KTree.node A10K2.u1587 (nat_lit 25773339) (nat_lit 10025055015) (nat_lit 0) A10K2.u1588 from rfl, allE_node, arows1587, irow1589, arows1588]
  all_goals rfl

theorem atot1589 : totK PA10K2 A10K2.u1589 = [0, 746479064816, 4297182639127, 7981496131939, 5084218736357, 864541330120, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1589 = KTree.node A10K2.u1587 (nat_lit 25773339) (nat_lit 10025055015) (nat_lit 0) A10K2.u1588 from rfl, totK_node, atot1587, atot1588]
  decide +kernel

theorem arows1592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1592 = true := by
  rw [show A10K2.u1592 = KTree.node A10K2.u1590 (nat_lit 25787802) (nat_lit 14487834767) (nat_lit 0) A10K2.u1591 from rfl, allE_node, arows1590, irow1592, arows1591]
  all_goals rfl

theorem atot1592 : totK PA10K2 A10K2.u1592 = [0, 595891457874, 3627795283521, 7705517074984, 6339139363331, 1648305450843, 88622189730, 0, 0, 0] := by
  rw [show A10K2.u1592 = KTree.node A10K2.u1590 (nat_lit 25787802) (nat_lit 14487834767) (nat_lit 0) A10K2.u1591 from rfl, totK_node, atot1590, atot1591]
  decide +kernel

theorem arows1599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1599 = true := by
  rw [show A10K2.u1599 = KTree.node A10K2.u1597 (nat_lit 25806186) (nat_lit 9940403154) (nat_lit 0) A10K2.u1598 from rfl, allE_node, arows1597, irow1599, arows1598]
  all_goals rfl

theorem atot1599 : totK PA10K2 A10K2.u1599 = [0, 0, 859777254630, 4482904826928, 7905196327788, 4653253834244, 812132859342, 37204059898, 0, 0] := by
  rw [show A10K2.u1599 = KTree.node A10K2.u1597 (nat_lit 25806186) (nat_lit 9940403154) (nat_lit 0) A10K2.u1598 from rfl, totK_node, atot1597, atot1598]
  decide +kernel

theorem arows1602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1602 = true := by
  rw [show A10K2.u1602 = KTree.node A10K2.u1600 (nat_lit 25823559) (nat_lit 5364189928) (nat_lit 0) A10K2.u1601 from rfl, allE_node, arows1600, irow1602, arows1601]
  all_goals rfl

theorem atot1602 : totK PA10K2 A10K2.u1602 = [0, 929693221955, 4356062048466, 7431749142384, 5281938470683, 1360578275924, 93750692321, 0, 0, 0] := by
  rw [show A10K2.u1602 = KTree.node A10K2.u1600 (nat_lit 25823559) (nat_lit 5364189928) (nat_lit 0) A10K2.u1601 from rfl, totK_node, atot1600, atot1601]
  decide +kernel

theorem arows1606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1606 = true := by
  rw [show A10K2.u1606 = KTree.node A10K2.u1604 (nat_lit 25836708) (nat_lit 11722107196) (nat_lit 0) A10K2.u1605 from rfl, allE_node, arows1604, irow1606, arows1605]
  all_goals rfl

theorem atot1606 : totK PA10K2 A10K2.u1606 = [0, 1219255596760, 5436472116351, 7785271265656, 4065054531863, 697110187910, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1606 = KTree.node A10K2.u1604 (nat_lit 25836708) (nat_lit 11722107196) (nat_lit 0) A10K2.u1605 from rfl, totK_node, atot1604, atot1605]
  decide +kernel

theorem arows1609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1609 = true := by
  rw [show A10K2.u1609 = KTree.node A10K2.u1607 (nat_lit 25856801) (nat_lit 9477304812) (nat_lit 0) A10K2.u1608 from rfl, allE_node, arows1607, irow1609, arows1608]
  all_goals rfl

theorem atot1609 : totK PA10K2 A10K2.u1609 = [0, 0, 2216130060370, 7710813446059, 7310090307922, 1754066332440, 97000438259, 0, 0, 0] := by
  rw [show A10K2.u1609 = KTree.node A10K2.u1607 (nat_lit 25856801) (nat_lit 9477304812) (nat_lit 0) A10K2.u1608 from rfl, totK_node, atot1607, atot1608]
  decide +kernel

theorem arows1614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1614 = true := by
  rw [show A10K2.u1614 = KTree.node A10K2.u1612 (nat_lit 25876800) (nat_lit 13445369445) (nat_lit 0) A10K2.u1613 from rfl, allE_node, arows1612, irow1614, arows1613]
  all_goals rfl

theorem atot1614 : totK PA10K2 A10K2.u1614 = [0, 0, 1418855812290, 6075066045644, 8011251291326, 3143239050782, 366248410154, 6354482628, 0, 0] := by
  rw [show A10K2.u1614 = KTree.node A10K2.u1612 (nat_lit 25876800) (nat_lit 13445369445) (nat_lit 0) A10K2.u1613 from rfl, totK_node, atot1612, atot1613]
  decide +kernel

theorem arows1617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1617 = true := by
  rw [show A10K2.u1617 = KTree.node A10K2.u1615 (nat_lit 26035699) (nat_lit 9015180604) (nat_lit 0) A10K2.u1616 from rfl, allE_node, arows1615, irow1617, arows1616]
  all_goals rfl

theorem atot1617 : totK PA10K2 A10K2.u1617 = [0, 0, 899888555222, 4567481812807, 7851523033863, 4706316196903, 813022502131, 38008422587, 0, 0] := by
  rw [show A10K2.u1617 = KTree.node A10K2.u1615 (nat_lit 26035699) (nat_lit 9015180604) (nat_lit 0) A10K2.u1616 from rfl, totK_node, atot1615, atot1616]
  decide +kernel

theorem arows1621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1621 = true := by
  rw [show A10K2.u1621 = KTree.node A10K2.u1619 (nat_lit 26083405) (nat_lit 5556177515) (nat_lit 0) A10K2.u1620 from rfl, allE_node, arows1619, irow1621, arows1620]
  all_goals rfl

theorem atot1621 : totK PA10K2 A10K2.u1621 = [0, 0, 1214702250694, 5553002479426, 8238704129633, 4134093468664, 559700773314, 12423235244, 0, 0] := by
  rw [show A10K2.u1621 = KTree.node A10K2.u1619 (nat_lit 26083405) (nat_lit 5556177515) (nat_lit 0) A10K2.u1620 from rfl, totK_node, atot1619, atot1620]
  decide +kernel

theorem arows1624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1624 = true := by
  rw [show A10K2.u1624 = KTree.node A10K2.u1622 (nat_lit 26097827) (nat_lit 10499862237) (nat_lit 0) A10K2.u1623 from rfl, allE_node, arows1622, irow1624, arows1623]
  all_goals rfl

theorem atot1624 : totK PA10K2 A10K2.u1624 = [0, 0, 1374233066420, 5654654131539, 7753803083673, 3756845346966, 578824601848, 31768748853, 0, 0] := by
  rw [show A10K2.u1624 = KTree.node A10K2.u1622 (nat_lit 26097827) (nat_lit 10499862237) (nat_lit 0) A10K2.u1623 from rfl, totK_node, atot1622, atot1623]
  decide +kernel

theorem arows1630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1630 = true := by
  rw [show A10K2.u1630 = KTree.node A10K2.u1628 (nat_lit 26118300) (nat_lit 11726668266) (nat_lit 0) A10K2.u1629 from rfl, allE_node, arows1628, irow1630, arows1629]
  all_goals rfl

theorem atot1630 : totK PA10K2 A10K2.u1630 = [0, 0, 0, 2710475580505, 8360286187438, 6489275269243, 1173080959287, 50219404490, 0, 0] := by
  rw [show A10K2.u1630 = KTree.node A10K2.u1628 (nat_lit 26118300) (nat_lit 11726668266) (nat_lit 0) A10K2.u1629 from rfl, totK_node, atot1628, atot1629]
  decide +kernel

theorem arows1633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1633 = true := by
  rw [show A10K2.u1633 = KTree.node A10K2.u1631 (nat_lit 26138944) (nat_lit 13264959328) (nat_lit 0) A10K2.u1632 from rfl, allE_node, arows1631, irow1633, arows1632]
  all_goals rfl

theorem atot1633 : totK PA10K2 A10K2.u1633 = [0, 812666997328, 3078376079659, 4009942331265, 4084543498940, 4608136144442, 1913353314897, 245602826600, 6239673734, 0] := by
  rw [show A10K2.u1633 = KTree.node A10K2.u1631 (nat_lit 26138944) (nat_lit 13264959328) (nat_lit 0) A10K2.u1632 from rfl, totK_node, atot1631, atot1632]
  decide +kernel

theorem arows1637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1637 = true := by
  rw [show A10K2.u1637 = KTree.node A10K2.u1635 (nat_lit 26232082) (nat_lit 14782276017) (nat_lit 0) A10K2.u1636 from rfl, allE_node, arows1635, irow1637, arows1636]
  all_goals rfl

theorem atot1637 : totK PA10K2 A10K2.u1637 = [0, 893025441187, 4519131517681, 7839885351667, 4816985284598, 861669274430, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u1637 = KTree.node A10K2.u1635 (nat_lit 26232082) (nat_lit 14782276017) (nat_lit 0) A10K2.u1636 from rfl, totK_node, atot1635, atot1636]
  decide +kernel

theorem arows1640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1640 = true := by
  rw [show A10K2.u1640 = KTree.node A10K2.u1638 (nat_lit 26247269) (nat_lit 6899524455) (nat_lit 0) A10K2.u1639 from rfl, allE_node, arows1638, irow1640, arows1639]
  all_goals rfl

theorem atot1640 : totK PA10K2 A10K2.u1640 = [0, 388272196882, 2914748258245, 7071764946227, 6711128617355, 2307930771400, 315833026003, 20060612110, 0, 0] := by
  rw [show A10K2.u1640 = KTree.node A10K2.u1638 (nat_lit 26247269) (nat_lit 6899524455) (nat_lit 0) A10K2.u1639 from rfl, totK_node, atot1638, atot1639]
  decide +kernel

theorem arows1645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1645 = true := by
  rw [show A10K2.u1645 = KTree.node A10K2.u1643 (nat_lit 26265820) (nat_lit 11176908802) (nat_lit 0) A10K2.u1644 from rfl, allE_node, arows1643, irow1645, arows1644]
  all_goals rfl

theorem atot1645 : totK PA10K2 A10K2.u1645 = [0, 0, 1204006399602, 5444506996424, 7922962028093, 3796026005730, 552520308070, 16136189093, 0, 0] := by
  rw [show A10K2.u1645 = KTree.node A10K2.u1643 (nat_lit 26265820) (nat_lit 11176908802) (nat_lit 0) A10K2.u1644 from rfl, totK_node, atot1643, atot1644]
  decide +kernel

theorem arows1648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1648 = true := by
  rw [show A10K2.u1648 = KTree.node A10K2.u1646 (nat_lit 26293494) (nat_lit 15766524011) (nat_lit 0) A10K2.u1647 from rfl, allE_node, arows1646, irow1648, arows1647]
  all_goals rfl

theorem atot1648 : totK PA10K2 A10K2.u1648 = [0, 1246455274452, 5183504363535, 7453788650733, 4477704599782, 1023961585361, 62598078170, 0, 0, 0] := by
  rw [show A10K2.u1648 = KTree.node A10K2.u1646 (nat_lit 26293494) (nat_lit 15766524011) (nat_lit 0) A10K2.u1647 from rfl, totK_node, atot1646, atot1647]
  decide +kernel

theorem arows1652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1652 = true := by
  rw [show A10K2.u1652 = KTree.node A10K2.u1650 (nat_lit 26305820) (nat_lit 11792231284) (nat_lit 0) A10K2.u1651 from rfl, allE_node, arows1650, irow1652, arows1651]
  all_goals rfl

theorem atot1652 : totK PA10K2 A10K2.u1652 = [0, 566126593814, 3884920459875, 8079330421645, 5528216575237, 1042386413910, 39796321239, 0, 0, 0] := by
  rw [show A10K2.u1652 = KTree.node A10K2.u1650 (nat_lit 26305820) (nat_lit 11792231284) (nat_lit 0) A10K2.u1651 from rfl, totK_node, atot1650, atot1651]
  decide +kernel

theorem arows1655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1655 = true := by
  rw [show A10K2.u1655 = KTree.node A10K2.u1653 (nat_lit 26329953) (nat_lit 8619877191) (nat_lit 0) A10K2.u1654 from rfl, allE_node, arows1653, irow1655, arows1654]
  all_goals rfl

theorem atot1655 : totK PA10K2 A10K2.u1655 = [0, 0, 968649238611, 5048075093990, 8220537569992, 4097410893464, 585025270381, 31082886609, 0, 0] := by
  rw [show A10K2.u1655 = KTree.node A10K2.u1653 (nat_lit 26329953) (nat_lit 8619877191) (nat_lit 0) A10K2.u1654 from rfl, totK_node, atot1653, atot1654]
  decide +kernel

theorem arows1663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1663 = true := by
  rw [show A10K2.u1663 = KTree.node A10K2.u1661 (nat_lit 26348658) (nat_lit 4689437619) (nat_lit 0) A10K2.u1662 from rfl, allE_node, arows1661, irow1663, arows1662]
  all_goals rfl

theorem atot1663 : totK PA10K2 A10K2.u1663 = [0, 1029843845153, 4595623468834, 7120237139947, 4650272378111, 1438688737358, 192292436754, 6121173289, 0, 0] := by
  rw [show A10K2.u1663 = KTree.node A10K2.u1661 (nat_lit 26348658) (nat_lit 4689437619) (nat_lit 0) A10K2.u1662 from rfl, totK_node, atot1661, atot1662]
  decide +kernel

theorem arows1666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1666 = true := by
  rw [show A10K2.u1666 = KTree.node A10K2.u1664 (nat_lit 26360485) (nat_lit 7192978334) (nat_lit 0) A10K2.u1665 from rfl, allE_node, arows1664, irow1666, arows1665]
  all_goals rfl

theorem atot1666 : totK PA10K2 A10K2.u1666 = [0, 1266487625915, 5472791017061, 7636074196019, 3822331954022, 609969523541, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1666 = KTree.node A10K2.u1664 (nat_lit 26360485) (nat_lit 7192978334) (nat_lit 0) A10K2.u1665 from rfl, totK_node, atot1664, atot1665]
  decide +kernel

theorem arows1670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1670 = true := by
  rw [show A10K2.u1670 = KTree.node A10K2.u1668 (nat_lit 26380565) (nat_lit 7022094326) (nat_lit 0) A10K2.u1669 from rfl, allE_node, arows1668, irow1670, arows1669]
  all_goals rfl

theorem atot1670 : totK PA10K2 A10K2.u1670 = [0, 0, 2287515090741, 7731486388868, 7137745475135, 1676890309045, 77608611860, 0, 0, 0] := by
  rw [show A10K2.u1670 = KTree.node A10K2.u1668 (nat_lit 26380565) (nat_lit 7022094326) (nat_lit 0) A10K2.u1669 from rfl, totK_node, atot1668, atot1669]
  decide +kernel

theorem arows1673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1673 = true := by
  rw [show A10K2.u1673 = KTree.node A10K2.u1671 (nat_lit 26399161) (nat_lit 6660125882) (nat_lit 0) A10K2.u1672 from rfl, allE_node, arows1671, irow1673, arows1672]
  all_goals rfl

theorem atot1673 : totK PA10K2 A10K2.u1673 = [0, 0, 1515536398022, 6156896143909, 7807741932756, 2944571372905, 354954654880, 6354482628, 0, 0] := by
  rw [show A10K2.u1673 = KTree.node A10K2.u1671 (nat_lit 26399161) (nat_lit 6660125882) (nat_lit 0) A10K2.u1672 from rfl, totK_node, atot1671, atot1672]
  decide +kernel

theorem arows1678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1678 = true := by
  rw [show A10K2.u1678 = KTree.node A10K2.u1676 (nat_lit 26493221) (nat_lit 7405569927) (nat_lit 0) A10K2.u1677 from rfl, allE_node, arows1676, irow1678, arows1677]
  all_goals rfl

theorem atot1678 : totK PA10K2 A10K2.u1678 = [0, 0, 919361389796, 4935876728828, 8105333756866, 4363175242291, 681673372337, 30818366867, 0, 0] := by
  rw [show A10K2.u1678 = KTree.node A10K2.u1676 (nat_lit 26493221) (nat_lit 7405569927) (nat_lit 0) A10K2.u1677 from rfl, totK_node, atot1676, atot1677]
  decide +kernel

theorem arows1681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1681 = true := by
  rw [show A10K2.u1681 = KTree.node A10K2.u1679 (nat_lit 26508294) (nat_lit 15385015361) (nat_lit 0) A10K2.u1680 from rfl, allE_node, arows1679, irow1681, arows1680]
  all_goals rfl

theorem atot1681 : totK PA10K2 A10K2.u1681 = [0, 0, 1263462520890, 5527565534409, 8090007817129, 4140505297330, 592608620694, 13207830636, 0, 0] := by
  rw [show A10K2.u1681 = KTree.node A10K2.u1679 (nat_lit 26508294) (nat_lit 15385015361) (nat_lit 0) A10K2.u1680 from rfl, totK_node, atot1679, atot1680]
  decide +kernel

theorem arows1685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1685 = true := by
  rw [show A10K2.u1685 = KTree.node A10K2.u1683 (nat_lit 26560356) (nat_lit 13654945502) (nat_lit 0) A10K2.u1684 from rfl, allE_node, arows1683, irow1685, arows1684]
  all_goals rfl

theorem atot1685 : totK PA10K2 A10K2.u1685 = [0, 0, 1046584309417, 4905838453281, 7788468532709, 4408756946686, 766866466296, 37807056478, 0, 0] := by
  rw [show A10K2.u1685 = KTree.node A10K2.u1683 (nat_lit 26560356) (nat_lit 13654945502) (nat_lit 0) A10K2.u1684 from rfl, totK_node, atot1683, atot1684]
  decide +kernel

theorem arows1688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1688 = true := by
  rw [show A10K2.u1688 = KTree.node A10K2.u1686 (nat_lit 26611655) (nat_lit 10963929162) (nat_lit 0) A10K2.u1687 from rfl, allE_node, arows1686, irow1688, arows1687]
  all_goals rfl

theorem atot1688 : totK PA10K2 A10K2.u1688 = [0, 0, 1142141236196, 5233259934152, 7905457965163, 3984156872193, 578615445850, 30074883546, 0, 0] := by
  rw [show A10K2.u1688 = KTree.node A10K2.u1686 (nat_lit 26611655) (nat_lit 10963929162) (nat_lit 0) A10K2.u1687 from rfl, totK_node, atot1686, atot1687]
  decide +kernel

theorem arows1694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1694 = true := by
  rw [show A10K2.u1694 = KTree.node A10K2.u1692 (nat_lit 26624062) (nat_lit 11554764298) (nat_lit 0) A10K2.u1693 from rfl, allE_node, arows1692, irow1694, arows1693]
  all_goals rfl

theorem atot1694 : totK PA10K2 A10K2.u1694 = [0, 0, 1140595278057, 5397956379790, 7804516833507, 3667460367796, 572664778452, 31003444686, 0, 0] := by
  rw [show A10K2.u1694 = KTree.node A10K2.u1692 (nat_lit 26624062) (nat_lit 11554764298) (nat_lit 0) A10K2.u1693 from rfl, totK_node, atot1692, atot1693]
  decide +kernel

theorem arows1697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1697 = true := by
  rw [show A10K2.u1697 = KTree.node A10K2.u1695 (nat_lit 26643532) (nat_lit 9982571948) (nat_lit 0) A10K2.u1696 from rfl, allE_node, arows1695, irow1697, arows1696]
  all_goals rfl

theorem atot1697 : totK PA10K2 A10K2.u1697 = [0, 0, 0, 2270788408793, 7713337561864, 6804866768223, 1573627684876, 93893887517, 0, 0] := by
  rw [show A10K2.u1697 = KTree.node A10K2.u1695 (nat_lit 26643532) (nat_lit 9982571948) (nat_lit 0) A10K2.u1696 from rfl, totK_node, atot1695, atot1696]
  decide +kernel

theorem arows1701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1701 = true := by
  rw [show A10K2.u1701 = KTree.node A10K2.u1699 (nat_lit 26663724) (nat_lit 13408271002) (nat_lit 0) A10K2.u1700 from rfl, allE_node, arows1699, irow1701, arows1700]
  all_goals rfl

theorem atot1701 : totK PA10K2 A10K2.u1701 = [0, 0, 857716201818, 3805525331318, 6499033066043, 5343706862797, 2015681985243, 291068676346, 6354482628, 0] := by
  rw [show A10K2.u1701 = KTree.node A10K2.u1699 (nat_lit 26663724) (nat_lit 13408271002) (nat_lit 0) A10K2.u1700 from rfl, totK_node, atot1699, atot1700]
  decide +kernel

theorem arows1704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1704 = true := by
  rw [show A10K2.u1704 = KTree.node A10K2.u1702 (nat_lit 27281057) (nat_lit 4565097215) (nat_lit 0) A10K2.u1703 from rfl, allE_node, arows1702, irow1704, arows1703]
  all_goals rfl

theorem atot1704 : totK PA10K2 A10K2.u1704 = [0, 0, 1036728720385, 4711346744186, 7620784752762, 4596772100639, 806258182882, 37186156514, 0, 0] := by
  rw [show A10K2.u1704 = KTree.node A10K2.u1702 (nat_lit 27281057) (nat_lit 4565097215) (nat_lit 0) A10K2.u1703 from rfl, totK_node, atot1702, atot1703]
  decide +kernel

theorem arows1709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1709 = true := by
  rw [show A10K2.u1709 = KTree.node A10K2.u1707 (nat_lit 27295117) (nat_lit 3517402125) (nat_lit 0) A10K2.u1708 from rfl, allE_node, arows1707, irow1709, arows1708]
  all_goals rfl

theorem atot1709 : totK PA10K2 A10K2.u1709 = [0, 0, 395296435550, 3425042255185, 8157143677489, 6628568788614, 1458079776001, 73985439776, 0, 0] := by
  rw [show A10K2.u1709 = KTree.node A10K2.u1707 (nat_lit 27295117) (nat_lit 3517402125) (nat_lit 0) A10K2.u1708 from rfl, totK_node, atot1707, atot1708]
  decide +kernel

theorem arows1712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1712 = true := by
  rw [show A10K2.u1712 = KTree.node A10K2.u1710 (nat_lit 27313301) (nat_lit 6714513073) (nat_lit 0) A10K2.u1711 from rfl, allE_node, arows1710, irow1712, arows1711]
  all_goals rfl

theorem atot1712 : totK PA10K2 A10K2.u1712 = [0, 0, 0, 921674065491, 4684567795647, 7793379692313, 4323432210590, 773111355735, 36196801203, 0] := by
  rw [show A10K2.u1712 = KTree.node A10K2.u1710 (nat_lit 27313301) (nat_lit 6714513073) (nat_lit 0) A10K2.u1711 from rfl, totK_node, atot1710, atot1711]
  decide +kernel

theorem arows1716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1716 = true := by
  rw [show A10K2.u1716 = KTree.node A10K2.u1714 (nat_lit 27396453) (nat_lit 7336690236) (nat_lit 0) A10K2.u1715 from rfl, allE_node, arows1714, irow1716, arows1715]
  all_goals rfl

theorem atot1716 : totK PA10K2 A10K2.u1716 = [0, 0, 836710839341, 4235636533536, 7824692726523, 5636008480087, 1264843716040, 80718512334, 0, 0] := by
  rw [show A10K2.u1716 = KTree.node A10K2.u1714 (nat_lit 27396453) (nat_lit 7336690236) (nat_lit 0) A10K2.u1715 from rfl, totK_node, atot1714, atot1715]
  decide +kernel

theorem arows1719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1719 = true := by
  rw [show A10K2.u1719 = KTree.node A10K2.u1717 (nat_lit 27410721) (nat_lit 9870704603) (nat_lit 0) A10K2.u1718 from rfl, allE_node, arows1717, irow1719, arows1718]
  all_goals rfl

theorem atot1719 : totK PA10K2 A10K2.u1719 = [0, 0, 1254395458895, 5652532160905, 7755935397723, 3474776119023, 441078180817, 11427838733, 0, 0] := by
  rw [show A10K2.u1719 = KTree.node A10K2.u1717 (nat_lit 27410721) (nat_lit 9870704603) (nat_lit 0) A10K2.u1718 from rfl, totK_node, atot1717, atot1718]
  decide +kernel

theorem arows1726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1726 = true := by
  rw [show A10K2.u1726 = KTree.node A10K2.u1724 (nat_lit 27430445) (nat_lit 5437391026) (nat_lit 0) A10K2.u1725 from rfl, allE_node, arows1724, irow1726, arows1725]
  all_goals rfl

theorem atot1726 : totK PA10K2 A10K2.u1726 = [0, 0, 0, 2125795920307, 7617225355852, 7365801068992, 1683108240837, 81752899290, 0, 0] := by
  rw [show A10K2.u1726 = KTree.node A10K2.u1724 (nat_lit 27430445) (nat_lit 5437391026) (nat_lit 0) A10K2.u1725 from rfl, totK_node, atot1724, atot1725]
  decide +kernel

theorem arows1729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1729 = true := by
  rw [show A10K2.u1729 = KTree.node A10K2.u1727 (nat_lit 27460109) (nat_lit 5603815240) (nat_lit 0) A10K2.u1728 from rfl, allE_node, arows1727, irow1729, arows1728]
  all_goals rfl

theorem atot1729 : totK PA10K2 A10K2.u1729 = [0, 0, 808480932972, 3731562694427, 6610822335875, 5738388328488, 2073617481589, 246497209322, 6354482628, 0] := by
  rw [show A10K2.u1729 = KTree.node A10K2.u1727 (nat_lit 27460109) (nat_lit 5603815240) (nat_lit 0) A10K2.u1728 from rfl, totK_node, atot1727, atot1728]
  decide +kernel

theorem arows1733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1733 = true := by
  rw [show A10K2.u1733 = KTree.node A10K2.u1731 (nat_lit 27488134) (nat_lit 15990001206) (nat_lit 0) A10K2.u1732 from rfl, allE_node, arows1731, irow1733, arows1732]
  all_goals rfl

theorem atot1733 : totK PA10K2 A10K2.u1733 = [0, 0, 797258379978, 4365345967232, 8187399554629, 5679843193818, 1214751755292, 62149755318, 0, 0] := by
  rw [show A10K2.u1733 = KTree.node A10K2.u1731 (nat_lit 27488134) (nat_lit 15990001206) (nat_lit 0) A10K2.u1732 from rfl, totK_node, atot1731, atot1732]
  decide +kernel

theorem arows1736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1736 = true := by
  rw [show A10K2.u1736 = KTree.node A10K2.u1734 (nat_lit 27516934) (nat_lit 15005840606) (nat_lit 0) A10K2.u1735 from rfl, allE_node, arows1734, irow1736, arows1735]
  all_goals rfl

theorem atot1736 : totK PA10K2 A10K2.u1736 = [0, 0, 414502387968, 2659054227994, 6672754702836, 7154769902199, 2796971571133, 343374553839, 6904928264, 0] := by
  rw [show A10K2.u1736 = KTree.node A10K2.u1734 (nat_lit 27516934) (nat_lit 15005840606) (nat_lit 0) A10K2.u1735 from rfl, totK_node, atot1734, atot1735]
  decide +kernel

theorem arows1741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1741 = true := by
  rw [show A10K2.u1741 = KTree.node A10K2.u1739 (nat_lit 27867910) (nat_lit 2249860030) (nat_lit 0) A10K2.u1740 from rfl, allE_node, arows1739, irow1741, arows1740]
  all_goals rfl

theorem atot1741 : totK PA10K2 A10K2.u1741 = [0, 0, 1173914314631, 5434640481158, 7918655005207, 4013387213047, 657600793279, 31768748853, 0, 0] := by
  rw [show A10K2.u1741 = KTree.node A10K2.u1739 (nat_lit 27867910) (nat_lit 2249860030) (nat_lit 0) A10K2.u1740 from rfl, totK_node, atot1739, atot1740]
  decide +kernel

theorem arows1744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1744 = true := by
  rw [show A10K2.u1744 = KTree.node A10K2.u1742 (nat_lit 27881415) (nat_lit 14303776902) (nat_lit 0) A10K2.u1743 from rfl, allE_node, arows1742, irow1744, arows1743]
  all_goals rfl

theorem atot1744 : totK PA10K2 A10K2.u1744 = [0, 0, 1152977523288, 5178246567650, 8041500948859, 4664585373894, 753087536634, 19280604132, 0, 0] := by
  rw [show A10K2.u1744 = KTree.node A10K2.u1742 (nat_lit 27881415) (nat_lit 14303776902) (nat_lit 0) A10K2.u1743 from rfl, totK_node, atot1742, atot1743]
  decide +kernel

theorem arows1748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1748 = true := by
  rw [show A10K2.u1748 = KTree.node A10K2.u1746 (nat_lit 27928840) (nat_lit 11747569976) (nat_lit 0) A10K2.u1747 from rfl, allE_node, arows1746, irow1748, arows1747]
  all_goals rfl

theorem atot1748 : totK PA10K2 A10K2.u1748 = [0, 0, 769927876336, 4335452636934, 8046405682816, 5114372232143, 869250565120, 42529659924, 0, 0] := by
  rw [show A10K2.u1748 = KTree.node A10K2.u1746 (nat_lit 27928840) (nat_lit 11747569976) (nat_lit 0) A10K2.u1747 from rfl, totK_node, atot1746, atot1747]
  decide +kernel

theorem arows1751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1751 = true := by
  rw [show A10K2.u1751 = KTree.node A10K2.u1749 (nat_lit 27940023) (nat_lit 12254561555) (nat_lit 0) A10K2.u1750 from rfl, allE_node, arows1749, irow1751, arows1750]
  all_goals rfl

theorem atot1751 : totK PA10K2 A10K2.u1751 = [0, 0, 815995094934, 4446037423744, 7865009964303, 4864011891131, 812974018534, 23367618958, 0, 0] := by
  rw [show A10K2.u1751 = KTree.node A10K2.u1749 (nat_lit 27940023) (nat_lit 12254561555) (nat_lit 0) A10K2.u1750 from rfl, totK_node, atot1749, atot1750]
  decide +kernel

theorem arows1757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1757 = true := by
  rw [show A10K2.u1757 = KTree.node A10K2.u1755 (nat_lit 27969179) (nat_lit 10025764973) (nat_lit 0) A10K2.u1756 from rfl, allE_node, arows1755, irow1757, arows1756]
  all_goals rfl

theorem atot1757 : totK PA10K2 A10K2.u1757 = [0, 0, 213371739588, 1887548835749, 6217639171551, 7442737567416, 2629574239116, 298661654793, 6354482628, 0] := by
  rw [show A10K2.u1757 = KTree.node A10K2.u1755 (nat_lit 27969179) (nat_lit 10025764973) (nat_lit 0) A10K2.u1756 from rfl, totK_node, atot1755, atot1756]
  decide +kernel

theorem arows1760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1760 = true := by
  rw [show A10K2.u1760 = KTree.node A10K2.u1758 (nat_lit 28316461) (nat_lit 6074769409) (nat_lit 0) A10K2.u1759 from rfl, allE_node, arows1758, irow1760, arows1759]
  all_goals rfl

theorem atot1760 : totK PA10K2 A10K2.u1760 = [0, 0, 1224367086551, 5407611515441, 7756014818601, 3973215930219, 651424118370, 30831673886, 0, 0] := by
  rw [show A10K2.u1760 = KTree.node A10K2.u1758 (nat_lit 28316461) (nat_lit 6074769409) (nat_lit 0) A10K2.u1759 from rfl, totK_node, atot1758, atot1759]
  decide +kernel

theorem arows1764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1764 = true := by
  rw [show A10K2.u1764 = KTree.node A10K2.u1762 (nat_lit 28337031) (nat_lit 14425336065) (nat_lit 0) A10K2.u1763 from rfl, allE_node, arows1762, irow1764, arows1763]
  all_goals rfl

theorem atot1764 : totK PA10K2 A10K2.u1764 = [0, 0, 636947652353, 4259753826281, 8212405104194, 5396047739984, 1036889161349, 44767738371, 0, 0] := by
  rw [show A10K2.u1764 = KTree.node A10K2.u1762 (nat_lit 28337031) (nat_lit 14425336065) (nat_lit 0) A10K2.u1763 from rfl, totK_node, atot1762, atot1763]
  decide +kernel

theorem arows1767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1767 = true := by
  rw [show A10K2.u1767 = KTree.node A10K2.u1765 (nat_lit 28351566) (nat_lit 10860953871) (nat_lit 0) A10K2.u1766 from rfl, allE_node, arows1765, irow1767, arows1766]
  all_goals rfl

theorem atot1767 : totK PA10K2 A10K2.u1767 = [0, 0, 0, 1167591679685, 5683468877137, 7968217296294, 3370422947206, 518791420703, 30220878370, 0] := by
  rw [show A10K2.u1767 = KTree.node A10K2.u1765 (nat_lit 28351566) (nat_lit 10860953871) (nat_lit 0) A10K2.u1766 from rfl, totK_node, atot1765, atot1766]
  decide +kernel

theorem arows1772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1772 = true := by
  rw [show A10K2.u1772 = KTree.node A10K2.u1770 (nat_lit 28387173) (nat_lit 7090834324) (nat_lit 0) A10K2.u1771 from rfl, allE_node, arows1770, irow1772, arows1771]
  all_goals rfl

theorem atot1772 : totK PA10K2 A10K2.u1772 = [0, 0, 763974328874, 3864654839384, 7164214551919, 5674058005785, 1735610544112, 206878224279, 5546304973, 0] := by
  rw [show A10K2.u1772 = KTree.node A10K2.u1770 (nat_lit 28387173) (nat_lit 7090834324) (nat_lit 0) A10K2.u1771 from rfl, totK_node, atot1770, atot1771]
  decide +kernel

theorem arows1775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1775 = true := by
  rw [show A10K2.u1775 = KTree.node A10K2.u1773 (nat_lit 28397859) (nat_lit 9146859342) (nat_lit 0) A10K2.u1774 from rfl, allE_node, arows1773, irow1775, arows1774]
  all_goals rfl

theorem atot1775 : totK PA10K2 A10K2.u1775 = [0, 0, 1047241538927, 5084107184594, 7955424042832, 4425274032888, 727086981297, 32978240608, 0, 0] := by
  rw [show A10K2.u1775 = KTree.node A10K2.u1773 (nat_lit 28397859) (nat_lit 9146859342) (nat_lit 0) A10K2.u1774 from rfl, totK_node, atot1773, atot1774]
  decide +kernel

theorem arows1779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1779 = true := by
  rw [show A10K2.u1779 = KTree.node A10K2.u1777 (nat_lit 28428650) (nat_lit 9839619679) (nat_lit 0) A10K2.u1778 from rfl, allE_node, arows1777, irow1779, arows1778]
  all_goals rfl

theorem atot1779 : totK PA10K2 A10K2.u1779 = [0, 0, 290234937362, 2475843692256, 6728192697616, 6913988336314, 2324337654785, 256465260086, 6121173289, 0] := by
  rw [show A10K2.u1779 = KTree.node A10K2.u1777 (nat_lit 28428650) (nat_lit 9839619679) (nat_lit 0) A10K2.u1778 from rfl, totK_node, atot1777, atot1778]
  decide +kernel

theorem arows1782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1782 = true := by
  rw [show A10K2.u1782 = KTree.node A10K2.u1780 (nat_lit 28449564) (nat_lit 11550216398) (nat_lit 0) A10K2.u1781 from rfl, allE_node, arows1780, irow1782, arows1781]
  all_goals rfl

theorem atot1782 : totK PA10K2 A10K2.u1782 = [0, 0, 1149925514430, 5251361914425, 7832722468064, 4108508858724, 615174006293, 30831673886, 0, 0] := by
  rw [show A10K2.u1782 = KTree.node A10K2.u1780 (nat_lit 28449564) (nat_lit 11550216398) (nat_lit 0) A10K2.u1781 from rfl, totK_node, atot1780, atot1781]
  decide +kernel

theorem arows1791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1791 = true := by
  rw [show A10K2.u1791 = KTree.node A10K2.u1789 (nat_lit 28461060) (nat_lit 12748852462) (nat_lit 0) A10K2.u1790 from rfl, allE_node, arows1789, irow1791, arows1790]
  all_goals rfl

theorem atot1791 : totK PA10K2 A10K2.u1791 = [0, 0, 845557281498, 4619328754562, 7939781772207, 4583074927534, 786000353054, 38123231481, 0, 0] := by
  rw [show A10K2.u1791 = KTree.node A10K2.u1789 (nat_lit 28461060) (nat_lit 12748852462) (nat_lit 0) A10K2.u1790 from rfl, totK_node, atot1789, atot1790]
  decide +kernel

theorem arows1794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1794 = true := by
  rw [show A10K2.u1794 = KTree.node A10K2.u1792 (nat_lit 28485917) (nat_lit 6421608984) (nat_lit 0) A10K2.u1793 from rfl, allE_node, arows1792, irow1794, arows1793]
  all_goals rfl

theorem atot1794 : totK PA10K2 A10K2.u1794 = [0, 0, 0, 1984962391916, 7360782279009, 7538259264553, 1855660743888, 121090445106, 0, 0] := by
  rw [show A10K2.u1794 = KTree.node A10K2.u1792 (nat_lit 28485917) (nat_lit 6421608984) (nat_lit 0) A10K2.u1793 from rfl, totK_node, atot1792, atot1793]
  decide +kernel

theorem arows1798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1798 = true := by
  rw [show A10K2.u1798 = KTree.node A10K2.u1796 (nat_lit 28575914) (nat_lit 11102505099) (nat_lit 0) A10K2.u1797 from rfl, allE_node, arows1796, irow1798, arows1797]
  all_goals rfl

theorem atot1798 : totK PA10K2 A10K2.u1798 = [0, 0, 0, 809847776486, 4619686655419, 8106546984967, 4377070949878, 751371479946, 36743231635, 0] := by
  rw [show A10K2.u1798 = KTree.node A10K2.u1796 (nat_lit 28575914) (nat_lit 11102505099) (nat_lit 0) A10K2.u1797 from rfl, totK_node, atot1796, atot1797]
  decide +kernel

theorem arows1801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1801 = true := by
  rw [show A10K2.u1801 = KTree.node A10K2.u1799 (nat_lit 28595432) (nat_lit 4806244903) (nat_lit 0) A10K2.u1800 from rfl, allE_node, arows1799, irow1801, arows1800]
  all_goals rfl

theorem atot1801 : totK PA10K2 A10K2.u1801 = [0, 0, 0, 1575507814078, 6425327854689, 7920760934745, 2922719247277, 306372215793, 6354482628, 0] := by
  rw [show A10K2.u1801 = KTree.node A10K2.u1799 (nat_lit 28595432) (nat_lit 4806244903) (nat_lit 0) A10K2.u1800 from rfl, totK_node, atot1799, atot1800]
  decide +kernel

theorem arows1806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1806 = true := by
  rw [show A10K2.u1806 = KTree.node A10K2.u1804 (nat_lit 28657697) (nat_lit 9876898653) (nat_lit 0) A10K2.u1805 from rfl, allE_node, arows1804, irow1806, arows1805]
  all_goals rfl

theorem atot1806 : totK PA10K2 A10K2.u1806 = [0, 0, 0, 1698450888461, 6551961228429, 7782971820029, 2791607443168, 324272975442, 6354482628, 0] := by
  rw [show A10K2.u1806 = KTree.node A10K2.u1804 (nat_lit 28657697) (nat_lit 9876898653) (nat_lit 0) A10K2.u1805 from rfl, totK_node, atot1804, atot1805]
  decide +kernel

theorem arows1809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1809 = true := by
  rw [show A10K2.u1809 = KTree.node A10K2.u1807 (nat_lit 28711168) (nat_lit 14397781664) (nat_lit 0) A10K2.u1808 from rfl, allE_node, arows1807, irow1809, arows1808]
  all_goals rfl

theorem atot1809 : totK PA10K2 A10K2.u1809 = [0, 0, 0, 1223033157361, 5635711401488, 7885036004836, 3389868329601, 534813766413, 30074883546, 0] := by
  rw [show A10K2.u1809 = KTree.node A10K2.u1807 (nat_lit 28711168) (nat_lit 14397781664) (nat_lit 0) A10K2.u1808 from rfl, totK_node, atot1807, atot1808]
  decide +kernel

theorem arows1813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1813 = true := by
  rw [show A10K2.u1813 = KTree.node A10K2.u1811 (nat_lit 28723768) (nat_lit 12710794095) (nat_lit 0) A10K2.u1812 from rfl, allE_node, arows1811, irow1813, arows1812]
  all_goals rfl

theorem atot1813 : totK PA10K2 A10K2.u1813 = [0, 0, 0, 836866021410, 4610914739507, 7920420338791, 4400544500791, 789672848794, 37227445626, 0] := by
  rw [show A10K2.u1813 = KTree.node A10K2.u1811 (nat_lit 28723768) (nat_lit 12710794095) (nat_lit 0) A10K2.u1812 from rfl, totK_node, atot1811, atot1812]
  decide +kernel

theorem arows1816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1816 = true := by
  rw [show A10K2.u1816 = KTree.node A10K2.u1814 (nat_lit 28755134) (nat_lit 10943114575) (nat_lit 2) A10K2.u1815 from rfl, allE_node, arows1814, irow1816, arows1815]
  all_goals rfl

theorem atot1816 : totK PA10K2 A10K2.u1816 = [0, 157526836586, 329480614415, 188003870903, 1841386792675, 6613472495284, 6734813326039, 2278122564857, 238650305755, 6354482628] := by
  rw [show A10K2.u1816 = KTree.node A10K2.u1814 (nat_lit 28755134) (nat_lit 10943114575) (nat_lit 2) A10K2.u1815 from rfl, totK_node, atot1814, atot1815]
  decide +kernel

theorem arows1822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1822 = true := by
  rw [show A10K2.u1822 = KTree.node A10K2.u1820 (nat_lit 29364778) (nat_lit 5551262875) (nat_lit 0) A10K2.u1821 from rfl, allE_node, arows1820, irow1822, arows1821]
  all_goals rfl

theorem atot1822 : totK PA10K2 A10K2.u1822 = [0, 1274928053297, 5494156138922, 7816220461097, 4024745026993, 668384254624, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1822 = KTree.node A10K2.u1820 (nat_lit 29364778) (nat_lit 5551262875) (nat_lit 0) A10K2.u1821 from rfl, totK_node, atot1820, atot1821]
  decide +kernel

theorem arows1825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1825 = true := by
  rw [show A10K2.u1825 = KTree.node A10K2.u1823 (nat_lit 29386387) (nat_lit 10807358917) (nat_lit 0) A10K2.u1824 from rfl, allE_node, arows1823, irow1825, arows1824]
  all_goals rfl

theorem atot1825 : totK PA10K2 A10K2.u1825 = [0, 867948227706, 4851298750225, 8373441666991, 4842257587994, 782950630238, 20158140256, 0, 0, 0] := by
  rw [show A10K2.u1825 = KTree.node A10K2.u1823 (nat_lit 29386387) (nat_lit 10807358917) (nat_lit 0) A10K2.u1824 from rfl, totK_node, atot1823, atot1824]
  decide +kernel

theorem arows1829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1829 = true := by
  rw [show A10K2.u1829 = KTree.node A10K2.u1827 (nat_lit 29396882) (nat_lit 12185572447) (nat_lit 0) A10K2.u1828 from rfl, allE_node, arows1827, irow1829, arows1828]
  all_goals rfl

theorem atot1829 : totK PA10K2 A10K2.u1829 = [0, 0, 1148593450866, 5411444343644, 7977954941576, 3978860237866, 655847275608, 30650496230, 0, 0] := by
  rw [show A10K2.u1829 = KTree.node A10K2.u1827 (nat_lit 29396882) (nat_lit 12185572447) (nat_lit 0) A10K2.u1828 from rfl, totK_node, atot1827, atot1828]
  decide +kernel

theorem arows1832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1832 = true := by
  rw [show A10K2.u1832 = KTree.node A10K2.u1830 (nat_lit 29418056) (nat_lit 13674404297) (nat_lit 0) A10K2.u1831 from rfl, allE_node, arows1830, irow1832, arows1831]
  all_goals rfl

theorem atot1832 : totK PA10K2 A10K2.u1832 = [0, 506452765222, 2756824740545, 6364029789732, 6860549537718, 2621105788422, 282560167263, 5546304973, 0, 0] := by
  rw [show A10K2.u1832 = KTree.node A10K2.u1830 (nat_lit 29418056) (nat_lit 13674404297) (nat_lit 0) A10K2.u1831 from rfl, totK_node, atot1830, atot1831]
  decide +kernel

theorem arows1837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1837 = true := by
  rw [show A10K2.u1837 = KTree.node A10K2.u1835 (nat_lit 29498801) (nat_lit 9204972428) (nat_lit 0) A10K2.u1836 from rfl, allE_node, arows1835, irow1837, arows1836]
  all_goals rfl

theorem atot1837 : totK PA10K2 A10K2.u1837 = [0, 1016920628206, 5208973237110, 8180409374093, 4264374857362, 673333311321, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u1837 = KTree.node A10K2.u1835 (nat_lit 29498801) (nat_lit 9204972428) (nat_lit 0) A10K2.u1836 from rfl, totK_node, atot1835, atot1836]
  decide +kernel

theorem arows1840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1840 = true := by
  rw [show A10K2.u1840 = KTree.node A10K2.u1838 (nat_lit 29527958) (nat_lit 15386836415) (nat_lit 0) A10K2.u1839 from rfl, allE_node, arows1838, irow1840, arows1839]
  all_goals rfl

theorem atot1840 : totK PA10K2 A10K2.u1840 = [0, 0, 1818393694890, 7150027143927, 7828234214325, 2161455420047, 133710342867, 0, 0, 0] := by
  rw [show A10K2.u1840 = KTree.node A10K2.u1838 (nat_lit 29527958) (nat_lit 15386836415) (nat_lit 0) A10K2.u1839 from rfl, totK_node, atot1838, atot1839]
  decide +kernel

theorem arows1844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1844 = true := by
  rw [show A10K2.u1844 = KTree.node A10K2.u1842 (nat_lit 29560831) (nat_lit 13966711711) (nat_lit 0) A10K2.u1843 from rfl, allE_node, arows1842, irow1844, arows1843]
  all_goals rfl

theorem atot1844 : totK PA10K2 A10K2.u1844 = [0, 1275483364437, 5189677517579, 7299988998643, 4388021143765, 1286927101236, 168336405883, 6354482628, 0, 0] := by
  rw [show A10K2.u1844 = KTree.node A10K2.u1842 (nat_lit 29560831) (nat_lit 13966711711) (nat_lit 0) A10K2.u1843 from rfl, totK_node, atot1842, atot1843]
  decide +kernel

theorem arows1847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1847 = true := by
  rw [show A10K2.u1847 = KTree.node A10K2.u1845 (nat_lit 29582678) (nat_lit 11886913796) (nat_lit 0) A10K2.u1846 from rfl, allE_node, arows1845, irow1847, arows1846]
  all_goals rfl

theorem atot1847 : totK PA10K2 A10K2.u1847 = [0, 946554254260, 4844973533359, 8192883516736, 4992013771925, 894938596633, 27377406697, 0, 0, 0] := by
  rw [show A10K2.u1847 = KTree.node A10K2.u1845 (nat_lit 29582678) (nat_lit 11886913796) (nat_lit 0) A10K2.u1846 from rfl, totK_node, atot1845, atot1846]
  decide +kernel

theorem arows1854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1854 = true := by
  rw [show A10K2.u1854 = KTree.node A10K2.u1852 (nat_lit 29593028) (nat_lit 7794905996) (nat_lit 0) A10K2.u1853 from rfl, allE_node, arows1852, irow1854, arows1853]
  all_goals rfl

theorem atot1854 : totK PA10K2 A10K2.u1854 = [0, 0, 1463268665476, 6058698420523, 8215285649176, 3678956648189, 430098598450, 6904928264, 0, 0] := by
  rw [show A10K2.u1854 = KTree.node A10K2.u1852 (nat_lit 29593028) (nat_lit 7794905996) (nat_lit 0) A10K2.u1853 from rfl, totK_node, atot1852, atot1853]
  decide +kernel

theorem arows1857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1857 = true := by
  rw [show A10K2.u1857 = KTree.node A10K2.u1855 (nat_lit 29615272) (nat_lit 11933677) (nat_lit 0) A10K2.u1856 from rfl, allE_node, arows1855, irow1857, arows1856]
  all_goals rfl

theorem atot1857 : totK PA10K2 A10K2.u1857 = [0, 0, 1083276213399, 5253719686481, 8276947406759, 4614288350430, 617018845250, 13113983930, 0, 0] := by
  rw [show A10K2.u1857 = KTree.node A10K2.u1855 (nat_lit 29615272) (nat_lit 11933677) (nat_lit 0) A10K2.u1856 from rfl, totK_node, atot1855, atot1856]
  decide +kernel

theorem arows1861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1861 = true := by
  rw [show A10K2.u1861 = KTree.node A10K2.u1859 (nat_lit 29625388) (nat_lit 11958293597) (nat_lit 0) A10K2.u1860 from rfl, allE_node, arows1859, irow1861, arows1860]
  all_goals rfl

theorem atot1861 : totK PA10K2 A10K2.u1861 = [0, 0, 887446199857, 4325054725043, 7569488979999, 5224537469888, 1278344202229, 85874841514, 0, 0] := by
  rw [show A10K2.u1861 = KTree.node A10K2.u1859 (nat_lit 29625388) (nat_lit 11958293597) (nat_lit 0) A10K2.u1860 from rfl, totK_node, atot1859, atot1860]
  decide +kernel

theorem arows1864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1864 = true := by
  rw [show A10K2.u1864 = KTree.node A10K2.u1862 (nat_lit 29645352) (nat_lit 11893589241) (nat_lit 0) A10K2.u1863 from rfl, allE_node, arows1862, irow1864, arows1863]
  all_goals rfl

theorem atot1864 : totK PA10K2 A10K2.u1864 = [0, 0, 1412956917732, 6107453767063, 8156981478776, 3338131238588, 341385338414, 5705019915, 0, 0] := by
  rw [show A10K2.u1864 = KTree.node A10K2.u1862 (nat_lit 29645352) (nat_lit 11893589241) (nat_lit 0) A10K2.u1863 from rfl, totK_node, atot1862, atot1863]
  decide +kernel

theorem arows1869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1869 = true := by
  rw [show A10K2.u1869 = KTree.node A10K2.u1867 (nat_lit 29657412) (nat_lit 13054302257) (nat_lit 0) A10K2.u1868 from rfl, allE_node, arows1867, irow1869, arows1868]
  all_goals rfl

theorem atot1869 : totK PA10K2 A10K2.u1869 = [0, 0, 0, 1417294730562, 5933821674712, 7715608674393, 3502490085111, 587846535122, 30605747850, 0] := by
  rw [show A10K2.u1869 = KTree.node A10K2.u1867 (nat_lit 29657412) (nat_lit 13054302257) (nat_lit 0) A10K2.u1868 from rfl, totK_node, atot1867, atot1868]
  decide +kernel

theorem arows1872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1872 = true := by
  rw [show A10K2.u1872 = KTree.node A10K2.u1870 (nat_lit 29678122) (nat_lit 7076824938) (nat_lit 0) A10K2.u1871 from rfl, allE_node, arows1870, irow1872, arows1871]
  all_goals rfl

theorem atot1872 : totK PA10K2 A10K2.u1872 = [0, 0, 307513935741, 2454095095715, 6582379163559, 7023221257738, 2549519829538, 289242433846, 5528811039, 0] := by
  rw [show A10K2.u1872 = KTree.node A10K2.u1870 (nat_lit 29678122) (nat_lit 7076824938) (nat_lit 0) A10K2.u1871 from rfl, totK_node, atot1870, atot1871]
  decide +kernel

theorem arows1876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1876 = true := by
  rw [show A10K2.u1876 = KTree.node A10K2.u1874 (nat_lit 29760257) (nat_lit 10111568244) (nat_lit 0) A10K2.u1875 from rfl, allE_node, arows1874, irow1876, arows1875]
  all_goals rfl

theorem atot1876 : totK PA10K2 A10K2.u1876 = [0, 0, 1226467116335, 5556525192820, 7939596306390, 3912652347079, 640798658264, 30831673886, 0, 0] := by
  rw [show A10K2.u1876 = KTree.node A10K2.u1874 (nat_lit 29760257) (nat_lit 10111568244) (nat_lit 0) A10K2.u1875 from rfl, totK_node, atot1874, atot1875]
  decide +kernel

theorem arows1879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1879 = true := by
  rw [show A10K2.u1879 = KTree.node A10K2.u1877 (nat_lit 29822399) (nat_lit 14297797703) (nat_lit 0) A10K2.u1878 from rfl, allE_node, arows1877, irow1879, arows1878]
  all_goals rfl

theorem atot1879 : totK PA10K2 A10K2.u1879 = [0, 0, 1055658002285, 5134723536204, 8211099574369, 4386841395254, 683600140967, 31667830797, 0, 0] := by
  rw [show A10K2.u1879 = KTree.node A10K2.u1877 (nat_lit 29822399) (nat_lit 14297797703) (nat_lit 0) A10K2.u1878 from rfl, totK_node, atot1877, atot1878]
  decide +kernel

theorem arows1885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1885 = true := by
  rw [show A10K2.u1885 = KTree.node A10K2.u1883 (nat_lit 29844406) (nat_lit 16784593185) (nat_lit 0) A10K2.u1884 from rfl, allE_node, arows1883, irow1885, arows1884]
  all_goals rfl

theorem atot1885 : totK PA10K2 A10K2.u1885 = [0, 0, 1166102113830, 5407118518978, 8350907135777, 4474276679082, 625384265410, 14004528958, 0, 0] := by
  rw [show A10K2.u1885 = KTree.node A10K2.u1883 (nat_lit 29844406) (nat_lit 16784593185) (nat_lit 0) A10K2.u1884 from rfl, totK_node, atot1883, atot1884]
  decide +kernel

theorem arows1888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1888 = true := by
  rw [show A10K2.u1888 = KTree.node A10K2.u1886 (nat_lit 29961060) (nat_lit 13706250501) (nat_lit 0) A10K2.u1887 from rfl, allE_node, arows1886, irow1888, arows1887]
  all_goals rfl

theorem atot1888 : totK PA10K2 A10K2.u1888 = [0, 847358390021, 3946598220083, 6431276188817, 4960382749362, 2600256657824, 747534994187, 55515214941, 0, 0] := by
  rw [show A10K2.u1888 = KTree.node A10K2.u1886 (nat_lit 29961060) (nat_lit 13706250501) (nat_lit 0) A10K2.u1887 from rfl, totK_node, atot1886, atot1887]
  decide +kernel

theorem arows1892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1892 = true := by
  rw [show A10K2.u1892 = KTree.node A10K2.u1890 (nat_lit 29974606) (nat_lit 10904956324) (nat_lit 0) A10K2.u1891 from rfl, allE_node, arows1890, irow1892, arows1891]
  all_goals rfl

theorem atot1892 : totK PA10K2 A10K2.u1892 = [0, 1363868382074, 5861263924560, 8150925819184, 3924523534541, 556384954535, 13195219453, 0, 0, 0] := by
  rw [show A10K2.u1892 = KTree.node A10K2.u1890 (nat_lit 29974606) (nat_lit 10904956324) (nat_lit 0) A10K2.u1891 from rfl, totK_node, atot1890, atot1891]
  decide +kernel

theorem arows1895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1895 = true := by
  rw [show A10K2.u1895 = KTree.node A10K2.u1893 (nat_lit 29993298) (nat_lit 14584827013) (nat_lit 0) A10K2.u1894 from rfl, allE_node, arows1893, irow1895, arows1894]
  all_goals rfl

theorem atot1895 : totK PA10K2 A10K2.u1895 = [0, 0, 1341488020718, 5808929203986, 7866983445922, 3746200035627, 621457066845, 31082886609, 0, 0] := by
  rw [show A10K2.u1895 = KTree.node A10K2.u1893 (nat_lit 29993298) (nat_lit 14584827013) (nat_lit 0) A10K2.u1894 from rfl, totK_node, atot1893, atot1894]
  decide +kernel

theorem arows1900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1900 = true := by
  rw [show A10K2.u1900 = KTree.node A10K2.u1898 (nat_lit 30006053) (nat_lit 7445950647) (nat_lit 0) A10K2.u1899 from rfl, allE_node, arows1898, irow1900, arows1899]
  all_goals rfl

theorem atot1900 : totK PA10K2 A10K2.u1900 = [0, 285766734819, 2139552922141, 6162868681784, 7561779074699, 3171148936382, 344879224256, 6121173289, 0, 0] := by
  rw [show A10K2.u1900 = KTree.node A10K2.u1898 (nat_lit 30006053) (nat_lit 7445950647) (nat_lit 0) A10K2.u1899 from rfl, totK_node, atot1898, atot1899]
  decide +kernel

theorem arows1903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1903 = true := by
  rw [show A10K2.u1903 = KTree.node A10K2.u1901 (nat_lit 30090644) (nat_lit 9054293972) (nat_lit 0) A10K2.u1902 from rfl, allE_node, arows1901, irow1903, arows1902]
  all_goals rfl

theorem atot1903 : totK PA10K2 A10K2.u1903 = [0, 1093787907821, 5210207997302, 8218099816188, 4603059504786, 839570588230, 39064973568, 0, 0, 0] := by
  rw [show A10K2.u1903 = KTree.node A10K2.u1901 (nat_lit 30090644) (nat_lit 9054293972) (nat_lit 0) A10K2.u1902 from rfl, totK_node, atot1901, atot1902]
  decide +kernel

theorem arows1907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1907 = true := by
  rw [show A10K2.u1907 = KTree.node A10K2.u1905 (nat_lit 30109112) (nat_lit 14231929522) (nat_lit 0) A10K2.u1906 from rfl, allE_node, arows1905, irow1907, arows1906]
  all_goals rfl

theorem atot1907 : totK PA10K2 A10K2.u1907 = [0, 866947050573, 4489463045970, 8057783432788, 5466982577593, 1079569779455, 31704442605, 0, 0, 0] := by
  rw [show A10K2.u1907 = KTree.node A10K2.u1905 (nat_lit 30109112) (nat_lit 14231929522) (nat_lit 0) A10K2.u1906 from rfl, totK_node, atot1905, atot1906]
  decide +kernel

theorem arows1910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1910 = true := by
  rw [show A10K2.u1910 = KTree.node A10K2.u1908 (nat_lit 30121202) (nat_lit 13806752898) (nat_lit 0) A10K2.u1909 from rfl, allE_node, arows1908, irow1910, arows1909]
  all_goals rfl

theorem atot1910 : totK PA10K2 A10K2.u1910 = [0, 0, 1378397471650, 5980664147409, 8304271101669, 3867137540161, 441020689862, 6904928264, 0, 0] := by
  rw [show A10K2.u1910 = KTree.node A10K2.u1908 (nat_lit 30121202) (nat_lit 13806752898) (nat_lit 0) A10K2.u1909 from rfl, totK_node, atot1908, atot1909]
  decide +kernel

theorem arows1918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1918 = true := by
  rw [show A10K2.u1918 = KTree.node A10K2.u1916 (nat_lit 30141631) (nat_lit 14180918075) (nat_lit 0) A10K2.u1917 from rfl, allE_node, arows1916, irow1918, arows1917]
  all_goals rfl

theorem atot1918 : totK PA10K2 A10K2.u1918 = [0, 0, 866236313379, 4558188840361, 8156020346252, 5326996701853, 915662035300, 25024441172, 0, 0] := by
  rw [show A10K2.u1918 = KTree.node A10K2.u1916 (nat_lit 30141631) (nat_lit 14180918075) (nat_lit 0) A10K2.u1917 from rfl, totK_node, atot1916, atot1917]
  decide +kernel

theorem arows1921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1921 = true := by
  rw [show A10K2.u1921 = KTree.node A10K2.u1919 (nat_lit 30225623) (nat_lit 12393994958) (nat_lit 0) A10K2.u1920 from rfl, allE_node, arows1919, irow1921, arows1920]
  all_goals rfl

theorem atot1921 : totK PA10K2 A10K2.u1921 = [0, 0, 1249930526881, 5237582609857, 7539022647634, 4389574132901, 1002690299936, 74901459239, 0, 0] := by
  rw [show A10K2.u1921 = KTree.node A10K2.u1919 (nat_lit 30225623) (nat_lit 12393994958) (nat_lit 0) A10K2.u1920 from rfl, totK_node, atot1919, atot1920]
  decide +kernel

theorem arows1925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1925 = true := by
  rw [show A10K2.u1925 = KTree.node A10K2.u1923 (nat_lit 30238486) (nat_lit 11525378562) (nat_lit 0) A10K2.u1924 from rfl, allE_node, arows1923, irow1925, arows1924]
  all_goals rfl

theorem atot1925 : totK PA10K2 A10K2.u1925 = [0, 0, 959341012135, 5038738302382, 8504502398419, 4745008420397, 670367942883, 13202416085, 0, 0] := by
  rw [show A10K2.u1925 = KTree.node A10K2.u1923 (nat_lit 30238486) (nat_lit 11525378562) (nat_lit 0) A10K2.u1924 from rfl, totK_node, atot1923, atot1924]
  decide +kernel

theorem arows1928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1928 = true := by
  rw [show A10K2.u1928 = KTree.node A10K2.u1926 (nat_lit 30258397) (nat_lit 5674131054) (nat_lit 0) A10K2.u1927 from rfl, allE_node, arows1926, irow1928, arows1927]
  all_goals rfl

theorem atot1928 : totK PA10K2 A10K2.u1928 = [0, 0, 0, 1694525473323, 6454731369736, 7786289707305, 3114525821952, 372967223869, 8047840951, 0] := by
  rw [show A10K2.u1928 = KTree.node A10K2.u1926 (nat_lit 30258397) (nat_lit 5674131054) (nat_lit 0) A10K2.u1927 from rfl, totK_node, atot1926, atot1927]
  decide +kernel

theorem arows1933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1933 = true := by
  rw [show A10K2.u1933 = KTree.node A10K2.u1931 (nat_lit 30346830) (nat_lit 10893499012) (nat_lit 0) A10K2.u1932 from rfl, allE_node, arows1931, irow1933, arows1932]
  all_goals rfl

theorem atot1933 : totK PA10K2 A10K2.u1933 = [0, 0, 1109129923598, 5054873946645, 7988478156388, 4900769088522, 1024660145859, 51842952317, 0, 0] := by
  rw [show A10K2.u1933 = KTree.node A10K2.u1931 (nat_lit 30346830) (nat_lit 10893499012) (nat_lit 0) A10K2.u1932 from rfl, totK_node, atot1931, atot1932]
  decide +kernel

theorem arows1936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1936 = true := by
  rw [show A10K2.u1936 = KTree.node A10K2.u1934 (nat_lit 30368014) (nat_lit 11211425880) (nat_lit 0) A10K2.u1935 from rfl, allE_node, arows1934, irow1936, arows1935]
  all_goals rfl

theorem atot1936 : totK PA10K2 A10K2.u1936 = [0, 0, 1136390135174, 5298656341671, 8229042467070, 4609157056691, 704825957902, 19853667457, 0, 0] := by
  rw [show A10K2.u1936 = KTree.node A10K2.u1934 (nat_lit 30368014) (nat_lit 11211425880) (nat_lit 0) A10K2.u1935 from rfl, totK_node, atot1934, atot1935]
  decide +kernel

theorem arows1940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1940 = true := by
  rw [show A10K2.u1940 = KTree.node A10K2.u1938 (nat_lit 30935105) (nat_lit 10335345372) (nat_lit 0) A10K2.u1939 from rfl, allE_node, arows1938, irow1940, arows1939]
  all_goals rfl

theorem atot1940 : totK PA10K2 A10K2.u1940 = [0, 819775609209, 3515633077302, 5773458875678, 5290208060584, 3239280341160, 844153663734, 56100664475, 0, 0] := by
  rw [show A10K2.u1940 = KTree.node A10K2.u1938 (nat_lit 30935105) (nat_lit 10335345372) (nat_lit 0) A10K2.u1939 from rfl, totK_node, atot1938, atot1939]
  decide +kernel

theorem arows1943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1943 = true := by
  rw [show A10K2.u1943 = KTree.node A10K2.u1941 (nat_lit 30957626) (nat_lit 10132090369) (nat_lit 0) A10K2.u1942 from rfl, allE_node, arows1941, irow1943, arows1942]
  all_goals rfl

theorem atot1943 : totK PA10K2 A10K2.u1943 = [0, 1307532830047, 5847673953566, 8332128425067, 3866744131960, 480349531192, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u1943 = KTree.node A10K2.u1941 (nat_lit 30957626) (nat_lit 10132090369) (nat_lit 0) A10K2.u1942 from rfl, totK_node, atot1941, atot1942]
  decide +kernel

theorem arows1949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1949 = true := by
  rw [show A10K2.u1949 = KTree.node A10K2.u1947 (nat_lit 30967968) (nat_lit 9074948959) (nat_lit 0) A10K2.u1948 from rfl, allE_node, arows1947, irow1949, arows1948]
  all_goals rfl

theorem atot1949 : totK PA10K2 A10K2.u1949 = [0, 0, 1355002426130, 5793244007837, 7961043399501, 3716761971436, 614228761202, 30650496230, 0, 0] := by
  rw [show A10K2.u1949 = KTree.node A10K2.u1947 (nat_lit 30967968) (nat_lit 9074948959) (nat_lit 0) A10K2.u1948 from rfl, totK_node, atot1947, atot1948]
  decide +kernel

theorem arows1952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1952 = true := by
  rw [show A10K2.u1952 = KTree.node A10K2.u1950 (nat_lit 30990898) (nat_lit 9985369790) (nat_lit 0) A10K2.u1951 from rfl, allE_node, arows1950, irow1952, arows1951]
  all_goals rfl

theorem atot1952 : totK PA10K2 A10K2.u1952 = [0, 409801074616, 2672403249041, 6764330191855, 7203745215457, 2461395232711, 191865076385, 0, 0, 0] := by
  rw [show A10K2.u1952 = KTree.node A10K2.u1950 (nat_lit 30990898) (nat_lit 9985369790) (nat_lit 0) A10K2.u1951 from rfl, totK_node, atot1950, atot1951]
  decide +kernel

theorem arows1956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1956 = true := by
  rw [show A10K2.u1956 = KTree.node A10K2.u1954 (nat_lit 31014277) (nat_lit 1254616384) (nat_lit 0) A10K2.u1955 from rfl, allE_node, arows1954, irow1956, arows1955]
  all_goals rfl

theorem atot1956 : totK PA10K2 A10K2.u1956 = [0, 1195654463806, 5445692287195, 8191264551156, 4344394652550, 710457454998, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u1956 = KTree.node A10K2.u1954 (nat_lit 31014277) (nat_lit 1254616384) (nat_lit 0) A10K2.u1955 from rfl, totK_node, atot1954, atot1955]
  decide +kernel

theorem arows1959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1959 = true := by
  rw [show A10K2.u1959 = KTree.node A10K2.u1957 (nat_lit 31030849) (nat_lit 9048588382) (nat_lit 0) A10K2.u1958 from rfl, allE_node, arows1957, irow1959, arows1958]
  all_goals rfl

theorem atot1959 : totK PA10K2 A10K2.u1959 = [0, 270838076424, 2717502780354, 7418784651584, 7315024960129, 2239369911392, 151324566406, 0, 0, 0] := by
  rw [show A10K2.u1959 = KTree.node A10K2.u1957 (nat_lit 31030849) (nat_lit 9048588382) (nat_lit 0) A10K2.u1958 from rfl, totK_node, atot1957, atot1958]
  decide +kernel

theorem arows1964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1964 = true := by
  rw [show A10K2.u1964 = KTree.node A10K2.u1962 (nat_lit 31056305) (nat_lit 9314812485) (nat_lit 0) A10K2.u1963 from rfl, allE_node, arows1962, irow1964, arows1963]
  all_goals rfl

theorem atot1964 : totK PA10K2 A10K2.u1964 = [0, 296996980728, 2035552752091, 5749540791966, 7448343865102, 3683942787838, 524200037805, 13576218110, 0, 0] := by
  rw [show A10K2.u1964 = KTree.node A10K2.u1962 (nat_lit 31056305) (nat_lit 9314812485) (nat_lit 0) A10K2.u1963 from rfl, totK_node, atot1962, atot1963]
  decide +kernel

theorem arows1967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1967 = true := by
  rw [show A10K2.u1967 = KTree.node A10K2.u1965 (nat_lit 31136769) (nat_lit 10511097145) (nat_lit 0) A10K2.u1966 from rfl, allE_node, arows1965, irow1967, arows1966]
  all_goals rfl

theorem atot1967 : totK PA10K2 A10K2.u1967 = [0, 1198545597644, 5469856079869, 8068103056937, 4182384580566, 646901310001, 25140510525, 0, 0, 0] := by
  rw [show A10K2.u1967 = KTree.node A10K2.u1965 (nat_lit 31136769) (nat_lit 10511097145) (nat_lit 0) A10K2.u1966 from rfl, totK_node, atot1965, atot1966]
  decide +kernel

theorem arows1971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1971 = true := by
  rw [show A10K2.u1971 = KTree.node A10K2.u1969 (nat_lit 31155933) (nat_lit 5346509369) (nat_lit 0) A10K2.u1970 from rfl, allE_node, arows1969, irow1971, arows1970]
  all_goals rfl

theorem atot1971 : totK PA10K2 A10K2.u1971 = [0, 893295087998, 4516627793022, 7960425834428, 5282340573756, 1022729096866, 32499029184, 0, 0, 0] := by
  rw [show A10K2.u1971 = KTree.node A10K2.u1969 (nat_lit 31155933) (nat_lit 5346509369) (nat_lit 0) A10K2.u1970 from rfl, totK_node, atot1969, atot1970]
  decide +kernel

theorem arows1974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1974 = true := by
  rw [show A10K2.u1974 = KTree.node A10K2.u1972 (nat_lit 31166134) (nat_lit 16488288833) (nat_lit 0) A10K2.u1973 from rfl, allE_node, arows1972, irow1974, arows1973]
  all_goals rfl

theorem atot1974 : totK PA10K2 A10K2.u1974 = [0, 0, 1411798600544, 5997162553025, 8089531395205, 3597415381299, 428734090413, 6904928264, 0, 0] := by
  rw [show A10K2.u1974 = KTree.node A10K2.u1972 (nat_lit 31166134) (nat_lit 16488288833) (nat_lit 0) A10K2.u1973 from rfl, totK_node, atot1972, atot1973]
  decide +kernel

theorem arows1981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1981 = true := by
  rw [show A10K2.u1981 = KTree.node A10K2.u1979 (nat_lit 31187442) (nat_lit 13125076133) (nat_lit 0) A10K2.u1980 from rfl, allE_node, arows1979, irow1981, arows1980]
  all_goals rfl

theorem atot1981 : totK PA10K2 A10K2.u1981 = [0, 0, 1200342640438, 5495131618609, 8265105991747, 4291346865910, 551145459141, 13113983930, 0, 0] := by
  rw [show A10K2.u1981 = KTree.node A10K2.u1979 (nat_lit 31187442) (nat_lit 13125076133) (nat_lit 0) A10K2.u1980 from rfl, totK_node, atot1979, atot1980]
  decide +kernel

theorem arows1984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1984 = true := by
  rw [show A10K2.u1984 = KTree.node A10K2.u1982 (nat_lit 31197447) (nat_lit 8955080670) (nat_lit 0) A10K2.u1983 from rfl, allE_node, arows1982, irow1984, arows1983]
  all_goals rfl

theorem atot1984 : totK PA10K2 A10K2.u1984 = [0, 0, 819276235637, 4223459744824, 7574450897690, 5351608871268, 1328125427160, 85823607806, 0, 0] := by
  rw [show A10K2.u1984 = KTree.node A10K2.u1982 (nat_lit 31197447) (nat_lit 8955080670) (nat_lit 0) A10K2.u1983 from rfl, totK_node, atot1982, atot1983]
  decide +kernel

theorem arows1988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1988 = true := by
  rw [show A10K2.u1988 = KTree.node A10K2.u1986 (nat_lit 31220214) (nat_lit 16660086782) (nat_lit 0) A10K2.u1987 from rfl, allE_node, arows1986, irow1988, arows1987]
  all_goals rfl

theorem atot1988 : totK PA10K2 A10K2.u1988 = [0, 0, 1306029577408, 5830560778536, 8337648603577, 3924318644863, 486120993419, 6853348008, 0, 0] := by
  rw [show A10K2.u1988 = KTree.node A10K2.u1986 (nat_lit 31220214) (nat_lit 16660086782) (nat_lit 0) A10K2.u1987 from rfl, totK_node, atot1986, atot1987]
  decide +kernel

theorem arows1991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1991 = true := by
  rw [show A10K2.u1991 = KTree.node A10K2.u1989 (nat_lit 31230804) (nat_lit 11558231196) (nat_lit 0) A10K2.u1990 from rfl, allE_node, arows1989, irow1991, arows1990]
  all_goals rfl

theorem atot1991 : totK PA10K2 A10K2.u1991 = [0, 0, 0, 1528815997198, 6316301461866, 8091194084885, 3280937466462, 383801694931, 7007974415, 0] := by
  rw [show A10K2.u1991 = KTree.node A10K2.u1989 (nat_lit 31230804) (nat_lit 11558231196) (nat_lit 0) A10K2.u1990 from rfl, totK_node, atot1989, atot1990]
  decide +kernel

theorem arows1996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1996 = true := by
  rw [show A10K2.u1996 = KTree.node A10K2.u1994 (nat_lit 31256449) (nat_lit 9791499850) (nat_lit 0) A10K2.u1995 from rfl, allE_node, arows1994, irow1996, arows1995]
  all_goals rfl

theorem atot1996 : totK PA10K2 A10K2.u1996 = [0, 0, 780638625629, 4190765773015, 7758739079755, 5670700543713, 1386220266213, 80321554933, 0, 0] := by
  rw [show A10K2.u1996 = KTree.node A10K2.u1994 (nat_lit 31256449) (nat_lit 9791499850) (nat_lit 0) A10K2.u1995 from rfl, totK_node, atot1994, atot1995]
  decide +kernel

theorem arows1999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1999 = true := by
  rw [show A10K2.u1999 = KTree.node A10K2.u1997 (nat_lit 31285811) (nat_lit 5455131535) (nat_lit 0) A10K2.u1998 from rfl, allE_node, arows1997, irow1999, arows1998]
  all_goals rfl

theorem atot1999 : totK PA10K2 A10K2.u1999 = [0, 0, 1093657370475, 5175448719423, 8233365638282, 4815245138786, 760392524916, 19856069994, 0, 0] := by
  rw [show A10K2.u1999 = KTree.node A10K2.u1997 (nat_lit 31285811) (nat_lit 5455131535) (nat_lit 0) A10K2.u1998 from rfl, totK_node, atot1997, atot1998]
  decide +kernel

theorem arows2003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2003 = true := by
  rw [show A10K2.u2003 = KTree.node A10K2.u2001 (nat_lit 31304922) (nat_lit 14066612926) (nat_lit 0) A10K2.u2002 from rfl, allE_node, arows2001, irow2003, arows2002]
  all_goals rfl

theorem atot2003 : totK PA10K2 A10K2.u2003 = [0, 0, 0, 1665713893539, 6625806956028, 8293017909226, 3174232683694, 323790952920, 7151180950, 0] := by
  rw [show A10K2.u2003 = KTree.node A10K2.u2001 (nat_lit 31304922) (nat_lit 14066612926) (nat_lit 0) A10K2.u2002 from rfl, totK_node, atot2001, atot2002]
  decide +kernel

theorem arows2006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2006 = true := by
  rw [show A10K2.u2006 = KTree.node A10K2.u2004 (nat_lit 31394052) (nat_lit 11069950854) (nat_lit 0) A10K2.u2005 from rfl, allE_node, arows2004, irow2006, arows2005]
  all_goals rfl

theorem atot2006 : totK PA10K2 A10K2.u2006 = [0, 0, 793614905159, 4182410111562, 7735360894043, 5622513974277, 1367401047320, 74623879111, 0, 0] := by
  rw [show A10K2.u2006 = KTree.node A10K2.u2004 (nat_lit 31394052) (nat_lit 11069950854) (nat_lit 0) A10K2.u2005 from rfl, totK_node, atot2004, atot2005]
  decide +kernel

theorem arows2012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2012 = true := by
  rw [show A10K2.u2012 = KTree.node A10K2.u2010 (nat_lit 31405910) (nat_lit 10513239227) (nat_lit 0) A10K2.u2011 from rfl, allE_node, arows2010, irow2012, arows2011]
  all_goals rfl

theorem atot2012 : totK PA10K2 A10K2.u2012 = [0, 0, 1546198776495, 6110085413431, 7831264232887, 3660849732231, 466935265879, 12219140272, 0, 0] := by
  rw [show A10K2.u2012 = KTree.node A10K2.u2010 (nat_lit 31405910) (nat_lit 10513239227) (nat_lit 0) A10K2.u2011 from rfl, totK_node, atot2010, atot2011]
  decide +kernel

theorem arows2015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2015 = true := by
  rw [show A10K2.u2015 = KTree.node A10K2.u2013 (nat_lit 31424213) (nat_lit 3018209954) (nat_lit 0) A10K2.u2014 from rfl, allE_node, arows2013, irow2015, arows2014]
  all_goals rfl

theorem atot2015 : totK PA10K2 A10K2.u2015 = [0, 0, 46039240014, 2202258630554, 7340884994494, 7718059827881, 2426370126103, 169441943548, 0, 0] := by
  rw [show A10K2.u2015 = KTree.node A10K2.u2013 (nat_lit 31424213) (nat_lit 3018209954) (nat_lit 0) A10K2.u2014 from rfl, totK_node, atot2013, atot2014]
  decide +kernel

theorem arows2019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2019 = true := by
  rw [show A10K2.u2019 = KTree.node A10K2.u2017 (nat_lit 31436742) (nat_lit 15559729183) (nat_lit 0) A10K2.u2018 from rfl, allE_node, arows2017, irow2019, arows2018]
  all_goals rfl

theorem atot2019 : totK PA10K2 A10K2.u2019 = [0, 0, 0, 1281228444681, 5774975170316, 8146080407203, 3850804094473, 489521603433, 12758098799, 0] := by
  rw [show A10K2.u2019 = KTree.node A10K2.u2017 (nat_lit 31436742) (nat_lit 15559729183) (nat_lit 0) A10K2.u2018 from rfl, totK_node, atot2017, atot2018]
  decide +kernel

theorem arows2022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2022 = true := by
  rw [show A10K2.u2022 = KTree.node A10K2.u2020 (nat_lit 31456698) (nat_lit 14274413006) (nat_lit 0) A10K2.u2021 from rfl, allE_node, arows2020, irow2022, arows2021]
  all_goals rfl

theorem atot2022 : totK PA10K2 A10K2.u2022 = [876250713213, 3080719290227, 3045804694393, 1117460714320, 2157637466912, 4614146058099, 3771674620406, 961189328672, 61018386929, 0] := by
  rw [show A10K2.u2022 = KTree.node A10K2.u2020 (nat_lit 31456698) (nat_lit 14274413006) (nat_lit 0) A10K2.u2021 from rfl, totK_node, atot2020, atot2021]
  decide +kernel

theorem arows2027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2027 = true := by
  rw [show A10K2.u2027 = KTree.node A10K2.u2025 (nat_lit 38356118) (nat_lit 14090307283) (nat_lit 0) A10K2.u2026 from rfl, allE_node, arows2025, irow2027, arows2026]
  all_goals rfl

theorem atot2027 : totK PA10K2 A10K2.u2027 = [722999960321, 4339079029628, 8106657507948, 4950917335516, 809489658763, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2027 = KTree.node A10K2.u2025 (nat_lit 38356118) (nat_lit 14090307283) (nat_lit 0) A10K2.u2026 from rfl, totK_node, atot2025, atot2026]
  decide +kernel

theorem arows2030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2030 = true := by
  rw [show A10K2.u2030 = KTree.node A10K2.u2028 (nat_lit 38367808) (nat_lit 11445097273) (nat_lit 0) A10K2.u2029 from rfl, allE_node, arows2028, irow2030, arows2029]
  all_goals rfl

theorem atot2030 : totK PA10K2 A10K2.u2030 = [785223503628, 4047765927693, 7642963658842, 5892074084499, 1546799825695, 94267787793, 0, 0, 0, 0] := by
  rw [show A10K2.u2030 = KTree.node A10K2.u2028 (nat_lit 38367808) (nat_lit 11445097273) (nat_lit 0) A10K2.u2029 from rfl, totK_node, atot2028, atot2029]
  decide +kernel

theorem arows2034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2034 = true := by
  rw [show A10K2.u2034 = KTree.node A10K2.u2032 (nat_lit 38386327) (nat_lit 10777501155) (nat_lit 0) A10K2.u2033 from rfl, allE_node, arows2032, irow2034, arows2033]
  all_goals rfl

theorem atot2034 : totK PA10K2 A10K2.u2034 = [0, 1222262612529, 5512396938377, 7796839725985, 3804407364238, 621581746788, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u2034 = KTree.node A10K2.u2032 (nat_lit 38386327) (nat_lit 10777501155) (nat_lit 0) A10K2.u2033 from rfl, totK_node, atot2032, atot2033]
  decide +kernel

theorem arows2037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2037 = true := by
  rw [show A10K2.u2037 = KTree.node A10K2.u2035 (nat_lit 38399217) (nat_lit 5933533854) (nat_lit 0) A10K2.u2036 from rfl, allE_node, arows2035, irow2037, arows2036]
  all_goals rfl

theorem atot2037 : totK PA10K2 A10K2.u2037 = [424355675811, 2736144132535, 6213100994265, 6500772950373, 2744866790631, 314721546038, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2037 = KTree.node A10K2.u2035 (nat_lit 38399217) (nat_lit 5933533854) (nat_lit 0) A10K2.u2036 from rfl, totK_node, atot2035, atot2036]
  decide +kernel

theorem arows2049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2049 = true := by
  rw [show A10K2.u2049 = KTree.node A10K2.u2047 (nat_lit 38417686) (nat_lit 11500460310) (nat_lit 0) A10K2.u2048 from rfl, allE_node, arows2047, irow2049, arows2048]
  all_goals rfl

theorem atot2049 : totK PA10K2 A10K2.u2049 = [1280074794421, 5238466808750, 7515800713425, 4401199911748, 819748482757, 37229241746, 0, 0, 0, 0] := by
  rw [show A10K2.u2049 = KTree.node A10K2.u2047 (nat_lit 38417686) (nat_lit 11500460310) (nat_lit 0) A10K2.u2048 from rfl, totK_node, atot2047, atot2048]
  decide +kernel

theorem arows2052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2052 = true := by
  rw [show A10K2.u2052 = KTree.node A10K2.u2050 (nat_lit 38436961) (nat_lit 10022573639) (nat_lit 0) A10K2.u2051 from rfl, allE_node, arows2050, irow2052, arows2051]
  all_goals rfl

theorem atot2052 : totK PA10K2 A10K2.u2052 = [298263154340, 3164232050494, 7750685224339, 6041726887146, 1366428417173, 70813303540, 0, 0, 0, 0] := by
  rw [show A10K2.u2052 = KTree.node A10K2.u2050 (nat_lit 38436961) (nat_lit 10022573639) (nat_lit 0) A10K2.u2051 from rfl, totK_node, atot2050, atot2051]
  decide +kernel

theorem arows2056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2056 = true := by
  rw [show A10K2.u2056 = KTree.node A10K2.u2054 (nat_lit 38457379) (nat_lit 7213023332) (nat_lit 0) A10K2.u2055 from rfl, allE_node, arows2054, irow2056, arows2055]
  all_goals rfl

theorem atot2056 : totK PA10K2 A10K2.u2056 = [476537513919, 2703822858463, 6285316804317, 6689679418719, 2544878485190, 322913992912, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2056 = KTree.node A10K2.u2054 (nat_lit 38457379) (nat_lit 7213023332) (nat_lit 0) A10K2.u2055 from rfl, totK_node, atot2054, atot2055]
  decide +kernel

theorem arows2059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2059 = true := by
  rw [show A10K2.u2059 = KTree.node A10K2.u2057 (nat_lit 38481457) (nat_lit 8894321435) (nat_lit 0) A10K2.u2058 from rfl, allE_node, arows2057, irow2059, arows2058]
  all_goals rfl

theorem atot2059 : totK PA10K2 A10K2.u2059 = [1040761456298, 4975403761643, 8105640200736, 4850470717630, 891643144618, 46171059895, 0, 0, 0, 0] := by
  rw [show A10K2.u2059 = KTree.node A10K2.u2057 (nat_lit 38481457) (nat_lit 8894321435) (nat_lit 0) A10K2.u2058 from rfl, totK_node, atot2057, atot2058]
  decide +kernel

theorem arows2064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2064 = true := by
  rw [show A10K2.u2064 = KTree.node A10K2.u2062 (nat_lit 38499742) (nat_lit 15508892991) (nat_lit 0) A10K2.u2063 from rfl, allE_node, arows2062, irow2064, arows2063]
  all_goals rfl

theorem atot2064 : totK PA10K2 A10K2.u2064 = [613328696870, 3661228587368, 7636707267297, 6329538900890, 1801247896966, 127974198260, 0, 0, 0, 0] := by
  rw [show A10K2.u2064 = KTree.node A10K2.u2062 (nat_lit 38499742) (nat_lit 15508892991) (nat_lit 0) A10K2.u2063 from rfl, totK_node, atot2062, atot2063]
  decide +kernel

theorem arows2067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2067 = true := by
  rw [show A10K2.u2067 = KTree.node A10K2.u2065 (nat_lit 38514244) (nat_lit 3549763749) (nat_lit 0) A10K2.u2066 from rfl, allE_node, arows2065, irow2067, arows2066]
  all_goals rfl

theorem atot2067 : totK PA10K2 A10K2.u2067 = [0, 1329980227440, 5663884708506, 8112735947622, 4168882029576, 598518647534, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2067 = KTree.node A10K2.u2065 (nat_lit 38514244) (nat_lit 3549763749) (nat_lit 0) A10K2.u2066 from rfl, totK_node, atot2065, atot2066]
  decide +kernel

theorem arows2071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2071 = true := by
  rw [show A10K2.u2071 = KTree.node A10K2.u2069 (nat_lit 38534207) (nat_lit 14216893575) (nat_lit 0) A10K2.u2070 from rfl, allE_node, arows2069, irow2071, arows2070]
  all_goals rfl

theorem atot2071 : totK PA10K2 A10K2.u2071 = [0, 1152293441149, 5092749011972, 7725584570222, 4601605560227, 1005344579950, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2071 = KTree.node A10K2.u2069 (nat_lit 38534207) (nat_lit 14216893575) (nat_lit 0) A10K2.u2070 from rfl, totK_node, atot2069, atot2070]
  decide +kernel

theorem arows2074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2074 = true := by
  rw [show A10K2.u2074 = KTree.node A10K2.u2072 (nat_lit 38617442) (nat_lit 11027884739) (nat_lit 0) A10K2.u2073 from rfl, allE_node, arows2072, irow2074, arows2073]
  all_goals rfl

theorem atot2074 : totK PA10K2 A10K2.u2074 = [0, 767053634955, 4641104533813, 8196206225634, 4662247385388, 730519613290, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2074 = KTree.node A10K2.u2072 (nat_lit 38617442) (nat_lit 11027884739) (nat_lit 0) A10K2.u2073 from rfl, totK_node, atot2072, atot2073]
  decide +kernel

theorem arows2080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2080 = true := by
  rw [show A10K2.u2080 = KTree.node A10K2.u2078 (nat_lit 38629786) (nat_lit 13658813218) (nat_lit 0) A10K2.u2079 from rfl, allE_node, arows2078, irow2080, arows2079]
  all_goals rfl

theorem atot2080 : totK PA10K2 A10K2.u2080 = [0, 784301050123, 4060591543192, 7765221359404, 5843641498977, 1374786434300, 73781283070, 0, 0, 0] := by
  rw [show A10K2.u2080 = KTree.node A10K2.u2078 (nat_lit 38629786) (nat_lit 13658813218) (nat_lit 0) A10K2.u2079 from rfl, totK_node, atot2078, atot2079]
  decide +kernel

theorem arows2083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2083 = true := by
  rw [show A10K2.u2083 = KTree.node A10K2.u2081 (nat_lit 38648476) (nat_lit 11611774975) (nat_lit 0) A10K2.u2082 from rfl, allE_node, arows2081, irow2083, arows2082]
  all_goals rfl

theorem atot2083 : totK PA10K2 A10K2.u2083 = [0, 0, 1262095370027, 5579702753365, 7615777264446, 3567805514906, 605208515852, 31018567651, 0, 0] := by
  rw [show A10K2.u2083 = KTree.node A10K2.u2081 (nat_lit 38648476) (nat_lit 11611774975) (nat_lit 0) A10K2.u2082 from rfl, totK_node, atot2081, atot2082]
  decide +kernel

theorem arows2087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2087 = true := by
  rw [show A10K2.u2087 = KTree.node A10K2.u2085 (nat_lit 38662029) (nat_lit 1013062007) (nat_lit 0) A10K2.u2086 from rfl, allE_node, arows2085, irow2087, arows2086]
  all_goals rfl

theorem atot2087 : totK PA10K2 A10K2.u2087 = [0, 733773351599, 3559529282525, 6556665636479, 5736162325524, 2112358218005, 244796735278, 5685526223, 0, 0] := by
  rw [show A10K2.u2087 = KTree.node A10K2.u2085 (nat_lit 38662029) (nat_lit 1013062007) (nat_lit 0) A10K2.u2086 from rfl, totK_node, atot2085, atot2086]
  decide +kernel

theorem arows2090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2090 = true := by
  rw [show A10K2.u2090 = KTree.node A10K2.u2088 (nat_lit 38680749) (nat_lit 6524584172) (nat_lit 0) A10K2.u2089 from rfl, allE_node, arows2088, irow2090, arows2089]
  all_goals rfl

theorem atot2090 : totK PA10K2 A10K2.u2090 = [0, 1268920272973, 5402646404140, 7683253033469, 4111198198469, 689122773085, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2090 = KTree.node A10K2.u2088 (nat_lit 38680749) (nat_lit 6524584172) (nat_lit 0) A10K2.u2089 from rfl, totK_node, atot2088, atot2089]
  decide +kernel

theorem arows2095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2095 = true := by
  rw [show A10K2.u2095 = KTree.node A10K2.u2093 (nat_lit 38701582) (nat_lit 4683677022) (nat_lit 0) A10K2.u2094 from rfl, allE_node, arows2093, irow2095, arows2094]
  all_goals rfl

theorem atot2095 : totK PA10K2 A10K2.u2095 = [0, 0, 2508640832134, 7950770233930, 6697914802392, 1386263285316, 57092737635, 0, 0, 0] := by
  rw [show A10K2.u2095 = KTree.node A10K2.u2093 (nat_lit 38701582) (nat_lit 4683677022) (nat_lit 0) A10K2.u2094 from rfl, totK_node, atot2093, atot2094]
  decide +kernel

theorem arows2098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2098 = true := by
  rw [show A10K2.u2098 = KTree.node A10K2.u2096 (nat_lit 38721874) (nat_lit 13648117361) (nat_lit 0) A10K2.u2097 from rfl, allE_node, arows2096, irow2098, arows2097]
  all_goals rfl

theorem atot2098 : totK PA10K2 A10K2.u2098 = [0, 603357570004, 3115492501012, 6612588544358, 6403664330412, 2226835464310, 252610801015, 6239673734, 0, 0] := by
  rw [show A10K2.u2098 = KTree.node A10K2.u2096 (nat_lit 38721874) (nat_lit 13648117361) (nat_lit 0) A10K2.u2097 from rfl, totK_node, atot2096, atot2097]
  decide +kernel

theorem arows2102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2102 = true := by
  rw [show A10K2.u2102 = KTree.node A10K2.u2100 (nat_lit 38745876) (nat_lit 12294741241) (nat_lit 0) A10K2.u2101 from rfl, allE_node, arows2100, irow2102, arows2101]
  all_goals rfl

theorem atot2102 : totK PA10K2 A10K2.u2102 = [0, 1357507950141, 5722835620964, 7935342524703, 4048573741543, 679927916032, 31285368086, 0, 0, 0] := by
  rw [show A10K2.u2102 = KTree.node A10K2.u2100 (nat_lit 38745876) (nat_lit 12294741241) (nat_lit 0) A10K2.u2101 from rfl, totK_node, atot2100, atot2101]
  decide +kernel

theorem arows2105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2105 = true := by
  rw [show A10K2.u2105 = KTree.node A10K2.u2103 (nat_lit 38764204) (nat_lit 4718913489) (nat_lit 0) A10K2.u2104 from rfl, allE_node, arows2103, irow2105, arows2104]
  all_goals rfl

theorem atot2105 : totK PA10K2 A10K2.u2105 = [560981842138, 2598174718585, 5074244181738, 6133389007815, 4198613475105, 1040680564555, 62382159641, 0, 0, 0] := by
  rw [show A10K2.u2105 = KTree.node A10K2.u2103 (nat_lit 38764204) (nat_lit 4718913489) (nat_lit 0) A10K2.u2104 from rfl, totK_node, atot2103, atot2104]
  decide +kernel

theorem arows2112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2112 = true := by
  rw [show A10K2.u2112 = KTree.node A10K2.u2110 (nat_lit 38817906) (nat_lit 11933677) (nat_lit 0) A10K2.u2111 from rfl, allE_node, arows2110, irow2112, arows2111]
  all_goals rfl

theorem atot2112 : totK PA10K2 A10K2.u2112 = [738817371650, 4138877991679, 7763099444964, 5210355302364, 995281926331, 43037386998, 0, 0, 0, 0] := by
  rw [show A10K2.u2112 = KTree.node A10K2.u2110 (nat_lit 38817906) (nat_lit 11933677) (nat_lit 0) A10K2.u2111 from rfl, totK_node, atot2110, atot2111]
  decide +kernel

theorem arows2115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2115 = true := by
  rw [show A10K2.u2115 = KTree.node A10K2.u2113 (nat_lit 38848552) (nat_lit 12517020101) (nat_lit 0) A10K2.u2114 from rfl, allE_node, arows2113, irow2115, arows2114]
  all_goals rfl

theorem atot2115 : totK PA10K2 A10K2.u2115 = [316846731414, 1795808215825, 4948030461222, 6999858779586, 3880970633493, 719208797475, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2115 = KTree.node A10K2.u2113 (nat_lit 38848552) (nat_lit 12517020101) (nat_lit 0) A10K2.u2114 from rfl, totK_node, atot2113, atot2114]
  decide +kernel

theorem arows2119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2119 = true := by
  rw [show A10K2.u2119 = KTree.node A10K2.u2117 (nat_lit 38877452) (nat_lit 11813284965) (nat_lit 0) A10K2.u2118 from rfl, allE_node, arows2117, irow2119, arows2118]
  all_goals rfl

theorem atot2119 : totK PA10K2 A10K2.u2119 = [1287679407729, 5465232261983, 7677671152237, 4081704731050, 690887243113, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2119 = KTree.node A10K2.u2117 (nat_lit 38877452) (nat_lit 11813284965) (nat_lit 0) A10K2.u2118 from rfl, totK_node, atot2117, atot2118]
  decide +kernel

theorem arows2122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2122 = true := by
  rw [show A10K2.u2122 = KTree.node A10K2.u2120 (nat_lit 38890894) (nat_lit 15185175319) (nat_lit 0) A10K2.u2121 from rfl, allE_node, arows2120, irow2122, arows2121]
  all_goals rfl

theorem atot2122 : totK PA10K2 A10K2.u2122 = [592283690039, 4005704527216, 8267860053716, 5691140806003, 1182953440002, 61595460661, 0, 0, 0, 0] := by
  rw [show A10K2.u2122 = KTree.node A10K2.u2120 (nat_lit 38890894) (nat_lit 15185175319) (nat_lit 0) A10K2.u2121 from rfl, totK_node, atot2120, atot2121]
  decide +kernel

theorem arows2127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2127 = true := by
  rw [show A10K2.u2127 = KTree.node A10K2.u2125 (nat_lit 38910116) (nat_lit 13604907954) (nat_lit 0) A10K2.u2126 from rfl, allE_node, arows2125, irow2127, arows2126]
  all_goals rfl

theorem atot2127 : totK PA10K2 A10K2.u2127 = [0, 1285919446045, 5537586831830, 7733457495052, 3847988475452, 636306022355, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u2127 = KTree.node A10K2.u2125 (nat_lit 38910116) (nat_lit 13604907954) (nat_lit 0) A10K2.u2126 from rfl, totK_node, atot2125, atot2126]
  decide +kernel

theorem arows2130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2130 = true := by
  rw [show A10K2.u2130 = KTree.node A10K2.u2128 (nat_lit 38923678) (nat_lit 15676680037) (nat_lit 0) A10K2.u2129 from rfl, allE_node, arows2128, irow2130, arows2129]
  all_goals rfl

theorem atot2130 : totK PA10K2 A10K2.u2130 = [582799510374, 2939221690177, 6078249558842, 6378345650259, 2758965333504, 314925463173, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2130 = KTree.node A10K2.u2128 (nat_lit 38923678) (nat_lit 15676680037) (nat_lit 0) A10K2.u2129 from rfl, totK_node, atot2128, atot2129]
  decide +kernel

theorem arows2134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2134 = true := by
  rw [show A10K2.u2134 = KTree.node A10K2.u2132 (nat_lit 38940117) (nat_lit 4529392385) (nat_lit 0) A10K2.u2133 from rfl, allE_node, arows2132, irow2134, arows2133]
  all_goals rfl

theorem atot2134 : totK PA10K2 A10K2.u2134 = [1008006057554, 4679239651253, 7566934094050, 4809256329124, 953019964407, 42529659924, 0, 0, 0, 0] := by
  rw [show A10K2.u2134 = KTree.node A10K2.u2132 (nat_lit 38940117) (nat_lit 4529392385) (nat_lit 0) A10K2.u2133 from rfl, totK_node, atot2132, atot2133]
  decide +kernel

theorem arows2137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2137 = true := by
  rw [show A10K2.u2137 = KTree.node A10K2.u2135 (nat_lit 38951091) (nat_lit 9842432020) (nat_lit 0) A10K2.u2136 from rfl, allE_node, arows2135, irow2137, arows2136]
  all_goals rfl

theorem atot2137 : totK PA10K2 A10K2.u2137 = [583317622402, 3921949108988, 7907900841869, 5346897090601, 1057023247714, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u2137 = KTree.node A10K2.u2135 (nat_lit 38951091) (nat_lit 9842432020) (nat_lit 0) A10K2.u2136 from rfl, totK_node, atot2135, atot2136]
  decide +kernel

theorem arows2143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2143 = true := by
  rw [show A10K2.u2143 = KTree.node A10K2.u2141 (nat_lit 38979283) (nat_lit 10592099614) (nat_lit 0) A10K2.u2142 from rfl, allE_node, arows2141, irow2143, arows2142]
  all_goals rfl

theorem atot2143 : totK PA10K2 A10K2.u2143 = [0, 1497570854393, 6095040260223, 7776819836965, 3000070521348, 355384936875, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2143 = KTree.node A10K2.u2141 (nat_lit 38979283) (nat_lit 10592099614) (nat_lit 0) A10K2.u2142 from rfl, totK_node, atot2141, atot2142]
  decide +kernel

theorem arows2146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2146 = true := by
  rw [show A10K2.u2146 = KTree.node A10K2.u2144 (nat_lit 39075841) (nat_lit 10581725467) (nat_lit 0) A10K2.u2145 from rfl, allE_node, arows2144, irow2146, arows2145]
  all_goals rfl

theorem atot2146 : totK PA10K2 A10K2.u2146 = [0, 1086026283077, 5295417787597, 7891991853286, 3980073622805, 644776294821, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u2146 = KTree.node A10K2.u2144 (nat_lit 39075841) (nat_lit 10581725467) (nat_lit 0) A10K2.u2145 from rfl, totK_node, atot2144, atot2145]
  decide +kernel

theorem arows2150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2150 = true := by
  rw [show A10K2.u2150 = KTree.node A10K2.u2148 (nat_lit 39136881) (nat_lit 5559145581) (nat_lit 0) A10K2.u2149 from rfl, allE_node, arows2148, irow2150, arows2149]
  all_goals rfl

theorem atot2150 : totK PA10K2 A10K2.u2150 = [0, 1021144311068, 4800824965618, 7716097180967, 4650514256881, 852272789238, 37807056478, 0, 0, 0] := by
  rw [show A10K2.u2150 = KTree.node A10K2.u2148 (nat_lit 39136881) (nat_lit 5559145581) (nat_lit 0) A10K2.u2149 from rfl, totK_node, atot2148, atot2149]
  decide +kernel

theorem arows2153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2153 = true := by
  rw [show A10K2.u2153 = KTree.node A10K2.u2151 (nat_lit 39147820) (nat_lit 13552313479) (nat_lit 0) A10K2.u2152 from rfl, allE_node, arows2151, irow2153, arows2152]
  all_goals rfl

theorem atot2153 : totK PA10K2 A10K2.u2153 = [0, 1175665518114, 5371309451554, 8163911599671, 4203128718524, 579946645903, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u2153 = KTree.node A10K2.u2151 (nat_lit 39147820) (nat_lit 13552313479) (nat_lit 0) A10K2.u2152 from rfl, totK_node, atot2151, atot2152]
  decide +kernel

theorem arows2158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2158 = true := by
  rw [show A10K2.u2158 = KTree.node A10K2.u2156 (nat_lit 39195501) (nat_lit 5300418178) (nat_lit 0) A10K2.u2157 from rfl, allE_node, arows2156, irow2158, arows2157]
  all_goals rfl

theorem atot2158 : totK PA10K2 A10K2.u2158 = [0, 1351021267949, 5702609242551, 7682783332598, 3659406922988, 580472219495, 30074883546, 0, 0, 0] := by
  rw [show A10K2.u2158 = KTree.node A10K2.u2156 (nat_lit 39195501) (nat_lit 5300418178) (nat_lit 0) A10K2.u2157 from rfl, totK_node, atot2156, atot2157]
  decide +kernel

theorem arows2161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2161 = true := by
  rw [show A10K2.u2161 = KTree.node A10K2.u2159 (nat_lit 39208120) (nat_lit 3217719769) (nat_lit 0) A10K2.u2160 from rfl, allE_node, arows2159, irow2161, arows2160]
  all_goals rfl

theorem atot2161 : totK PA10K2 A10K2.u2161 = [0, 820492422360, 4634050702516, 8102889000063, 4404332455337, 652016171742, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u2161 = KTree.node A10K2.u2159 (nat_lit 39208120) (nat_lit 3217719769) (nat_lit 0) A10K2.u2160 from rfl, totK_node, atot2159, atot2160]
  decide +kernel

theorem arows2165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2165 = true := by
  rw [show A10K2.u2165 = KTree.node A10K2.u2163 (nat_lit 39233632) (nat_lit 12548770865) (nat_lit 0) A10K2.u2164 from rfl, allE_node, arows2163, irow2165, arows2164]
  all_goals rfl

theorem atot2165 : totK PA10K2 A10K2.u2165 = [0, 0, 2122099730394, 7316078774851, 7085603447970, 1811119838376, 119348013684, 0, 0, 0] := by
  rw [show A10K2.u2165 = KTree.node A10K2.u2163 (nat_lit 39233632) (nat_lit 12548770865) (nat_lit 0) A10K2.u2164 from rfl, totK_node, atot2163, atot2164]
  decide +kernel

theorem arows2168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2168 = true := by
  rw [show A10K2.u2168 = KTree.node A10K2.u2166 (nat_lit 39324745) (nat_lit 9546374784) (nat_lit 0) A10K2.u2167 from rfl, allE_node, arows2166, irow2168, arows2167]
  all_goals rfl

theorem atot2168 : totK PA10K2 A10K2.u2168 = [953763886815, 3852874007705, 5409407825603, 4022369985097, 3323618789314, 1636692136229, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u2168 = KTree.node A10K2.u2166 (nat_lit 39324745) (nat_lit 9546374784) (nat_lit 0) A10K2.u2167 from rfl, totK_node, atot2166, atot2167]
  decide +kernel

theorem arows2176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2176 = true := by
  rw [show A10K2.u2176 = KTree.node A10K2.u2174 (nat_lit 39353415) (nat_lit 11210411356) (nat_lit 0) A10K2.u2175 from rfl, allE_node, arows2174, irow2176, arows2175]
  all_goals rfl

theorem atot2176 : totK PA10K2 A10K2.u2176 = [432469934381, 3219004612408, 7564441494552, 6963179510845, 2101895568434, 143635975025, 0, 0, 0, 0] := by
  rw [show A10K2.u2176 = KTree.node A10K2.u2174 (nat_lit 39353415) (nat_lit 11210411356) (nat_lit 0) A10K2.u2175 from rfl, totK_node, atot2174, atot2175]
  decide +kernel

theorem arows2179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2179 = true := by
  rw [show A10K2.u2179 = KTree.node A10K2.u2177 (nat_lit 39382712) (nat_lit 11359994883) (nat_lit 0) A10K2.u2178 from rfl, allE_node, arows2177, irow2179, arows2178]
  all_goals rfl

theorem atot2179 : totK PA10K2 A10K2.u2179 = [846901670217, 4018625757677, 6909380962083, 5600340827184, 2231194643253, 402157778273, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2179 = KTree.node A10K2.u2177 (nat_lit 39382712) (nat_lit 11359994883) (nat_lit 0) A10K2.u2178 from rfl, totK_node, atot2177, atot2178]
  decide +kernel

theorem arows2183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2183 = true := by
  rw [show A10K2.u2183 = KTree.node A10K2.u2181 (nat_lit 39405715) (nat_lit 10817113888) (nat_lit 0) A10K2.u2182 from rfl, allE_node, arows2181, irow2183, arows2182]
  all_goals rfl

theorem atot2183 : totK PA10K2 A10K2.u2183 = [1052477690864, 4925686019953, 7821569265636, 4666955774510, 868159967550, 38123231481, 0, 0, 0, 0] := by
  rw [show A10K2.u2183 = KTree.node A10K2.u2181 (nat_lit 39405715) (nat_lit 10817113888) (nat_lit 0) A10K2.u2182 from rfl, totK_node, atot2181, atot2182]
  decide +kernel

theorem arows2186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2186 = true := by
  rw [show A10K2.u2186 = KTree.node A10K2.u2184 (nat_lit 39419109) (nat_lit 5007967293) (nat_lit 0) A10K2.u2185 from rfl, allE_node, arows2184, irow2186, arows2185]
  all_goals rfl

theorem atot2186 : totK PA10K2 A10K2.u2186 = [319364795913, 3046186632096, 7877198989145, 6947248745230, 1751266981710, 95502021083, 0, 0, 0, 0] := by
  rw [show A10K2.u2186 = KTree.node A10K2.u2184 (nat_lit 39419109) (nat_lit 5007967293) (nat_lit 0) A10K2.u2185 from rfl, totK_node, atot2184, atot2185]
  decide +kernel

theorem arows2191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2191 = true := by
  rw [show A10K2.u2191 = KTree.node A10K2.u2189 (nat_lit 39438092) (nat_lit 11379265400) (nat_lit 0) A10K2.u2190 from rfl, allE_node, arows2189, irow2191, arows2190]
  all_goals rfl

theorem atot2191 : totK PA10K2 A10K2.u2191 = [0, 938727236312, 4747089137996, 7918706240768, 4643773197610, 812762740353, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2191 = KTree.node A10K2.u2189 (nat_lit 39438092) (nat_lit 11379265400) (nat_lit 0) A10K2.u2190 from rfl, totK_node, atot2189, atot2190]
  decide +kernel

theorem arows2194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2194 = true := by
  rw [show A10K2.u2194 = KTree.node A10K2.u2192 (nat_lit 39521736) (nat_lit 13975665971) (nat_lit 0) A10K2.u2193 from rfl, allE_node, arows2192, irow2194, arows2193]
  all_goals rfl

theorem atot2194 : totK PA10K2 A10K2.u2194 = [1030278054533, 4683464344789, 7630306379873, 5256750741461, 1358610633329, 95818979617, 0, 0, 0, 0] := by
  rw [show A10K2.u2194 = KTree.node A10K2.u2192 (nat_lit 39521736) (nat_lit 13975665971) (nat_lit 0) A10K2.u2193 from rfl, totK_node, atot2192, atot2193]
  decide +kernel

theorem arows2198 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2198 = true := by
  rw [show A10K2.u2198 = KTree.node A10K2.u2196 (nat_lit 39533782) (nat_lit 15177660555) (nat_lit 0) A10K2.u2197 from rfl, allE_node, arows2196, irow2198, arows2197]
  all_goals rfl

theorem atot2198 : totK PA10K2 A10K2.u2198 = [1254436619767, 5571532129800, 8091560091820, 4232317466173, 697473847712, 31677228370, 0, 0, 0, 0] := by
  rw [show A10K2.u2198 = KTree.node A10K2.u2196 (nat_lit 39533782) (nat_lit 15177660555) (nat_lit 0) A10K2.u2197 from rfl, totK_node, atot2196, atot2197]
  decide +kernel

theorem arows2201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2201 = true := by
  rw [show A10K2.u2201 = KTree.node A10K2.u2199 (nat_lit 39551493) (nat_lit 6324276604) (nat_lit 0) A10K2.u2200 from rfl, allE_node, arows2199, irow2201, arows2200]
  all_goals rfl

theorem atot2201 : totK PA10K2 A10K2.u2201 = [0, 1644708008063, 6479288370670, 8061366399767, 3315330004765, 393933460750, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2201 = KTree.node A10K2.u2199 (nat_lit 39551493) (nat_lit 6324276604) (nat_lit 0) A10K2.u2200 from rfl, totK_node, atot2199, atot2200]
  decide +kernel

theorem arows2207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2207 = true := by
  rw [show A10K2.u2207 = KTree.node A10K2.u2205 (nat_lit 39565463) (nat_lit 11836517766) (nat_lit 0) A10K2.u2206 from rfl, allE_node, arows2205, irow2207, arows2206]
  all_goals rfl

theorem atot2207 : totK PA10K2 A10K2.u2207 = [0, 1477734292704, 6247345370950, 8159808274507, 3515074187930, 396086848056, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2207 = KTree.node A10K2.u2205 (nat_lit 39565463) (nat_lit 11836517766) (nat_lit 0) A10K2.u2206 from rfl, totK_node, atot2205, atot2206]
  decide +kernel

theorem arows2210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2210 = true := by
  rw [show A10K2.u2210 = KTree.node A10K2.u2208 (nat_lit 39583816) (nat_lit 13804082660) (nat_lit 0) A10K2.u2209 from rfl, allE_node, arows2208, irow2210, arows2209]
  all_goals rfl

theorem atot2210 : totK PA10K2 A10K2.u2210 = [0, 591601212612, 3846991786654, 8002035738237, 6003795569207, 1393428892398, 86443380410, 0, 0, 0] := by
  rw [show A10K2.u2210 = KTree.node A10K2.u2208 (nat_lit 39583816) (nat_lit 13804082660) (nat_lit 0) A10K2.u2209 from rfl, totK_node, atot2208, atot2209]
  decide +kernel

theorem arows2214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2214 = true := by
  rw [show A10K2.u2214 = KTree.node A10K2.u2212 (nat_lit 39613024) (nat_lit 13310380189) (nat_lit 0) A10K2.u2213 from rfl, allE_node, arows2212, irow2214, arows2213]
  all_goals rfl

theorem atot2214 : totK PA10K2 A10K2.u2214 = [0, 792629982373, 4298202390786, 7919125199086, 5835278450492, 1444799298031, 87926673087, 0, 0, 0] := by
  rw [show A10K2.u2214 = KTree.node A10K2.u2212 (nat_lit 39613024) (nat_lit 13310380189) (nat_lit 0) A10K2.u2213 from rfl, totK_node, atot2212, atot2213]
  decide +kernel

theorem arows2217 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2217 = true := by
  rw [show A10K2.u2217 = KTree.node A10K2.u2215 (nat_lit 39643063) (nat_lit 15022155598) (nat_lit 0) A10K2.u2216 from rfl, allE_node, arows2215, irow2217, arows2216]
  all_goals rfl

theorem atot2217 : totK PA10K2 A10K2.u2217 = [0, 762731751758, 3343992492202, 6320398525959, 6398980790869, 2727208178060, 349574644938, 7007974415, 0, 0] := by
  rw [show A10K2.u2217 = KTree.node A10K2.u2215 (nat_lit 39643063) (nat_lit 15022155598) (nat_lit 0) A10K2.u2216 from rfl, totK_node, atot2215, atot2216]
  decide +kernel

theorem arows2222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2222 = true := by
  rw [show A10K2.u2222 = KTree.node A10K2.u2220 (nat_lit 39666981) (nat_lit 7408626806) (nat_lit 0) A10K2.u2221 from rfl, allE_node, arows2220, irow2222, arows2221]
  all_goals rfl

theorem atot2222 : totK PA10K2 A10K2.u2222 = [0, 825927001558, 4606320407403, 8111347611840, 4923676875913, 859256187973, 37546598172, 0, 0, 0] := by
  rw [show A10K2.u2222 = KTree.node A10K2.u2220 (nat_lit 39666981) (nat_lit 7408626806) (nat_lit 0) A10K2.u2221 from rfl, totK_node, atot2220, atot2221]
  decide +kernel

theorem arows2225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2225 = true := by
  rw [show A10K2.u2225 = KTree.node A10K2.u2223 (nat_lit 39679390) (nat_lit 15508892991) (nat_lit 0) A10K2.u2224 from rfl, allE_node, arows2223, irow2225, arows2224]
  all_goals rfl

theorem atot2225 : totK PA10K2 A10K2.u2225 = [0, 614826028692, 3732732493788, 7808921844671, 6202913296613, 1524894449024, 88420430393, 0, 0, 0] := by
  rw [show A10K2.u2225 = KTree.node A10K2.u2223 (nat_lit 39679390) (nat_lit 15508892991) (nat_lit 0) A10K2.u2224 from rfl, totK_node, atot2223, atot2224]
  decide +kernel

theorem arows2229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2229 = true := by
  rw [show A10K2.u2229 = KTree.node A10K2.u2227 (nat_lit 39699960) (nat_lit 5577186326) (nat_lit 0) A10K2.u2228 from rfl, allE_node, arows2227, irow2229, arows2228]
  all_goals rfl

theorem atot2229 : totK PA10K2 A10K2.u2229 = [0, 0, 1661802237205, 6494515456732, 8024983067188, 3174938640071, 347127765628, 7151180950, 0, 0] := by
  rw [show A10K2.u2229 = KTree.node A10K2.u2227 (nat_lit 39699960) (nat_lit 5577186326) (nat_lit 0) A10K2.u2228 from rfl, totK_node, atot2227, atot2228]
  decide +kernel

theorem arows2232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2232 = true := by
  rw [show A10K2.u2232 = KTree.node A10K2.u2230 (nat_lit 39787022) (nat_lit 11149247314) (nat_lit 0) A10K2.u2231 from rfl, allE_node, arows2230, irow2232, arows2231]
  all_goals rfl

theorem atot2232 : totK PA10K2 A10K2.u2232 = [0, 1410410053387, 5920738910939, 8021648100902, 3915736698389, 727513019230, 49666398741, 0, 0, 0] := by
  rw [show A10K2.u2232 = KTree.node A10K2.u2230 (nat_lit 39787022) (nat_lit 11149247314) (nat_lit 0) A10K2.u2231 from rfl, totK_node, atot2230, atot2231]
  decide +kernel

theorem arows2239 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2239 = true := by
  rw [show A10K2.u2239 = KTree.node A10K2.u2237 (nat_lit 39806624) (nat_lit 1809143822) (nat_lit 0) A10K2.u2238 from rfl, allE_node, arows2237, irow2239, arows2238]
  all_goals rfl

theorem atot2239 : totK PA10K2 A10K2.u2239 = [0, 872810143373, 4517926810846, 8017655234449, 5332648546144, 946992739145, 25872399942, 0, 0, 0] := by
  rw [show A10K2.u2239 = KTree.node A10K2.u2237 (nat_lit 39806624) (nat_lit 1809143822) (nat_lit 0) A10K2.u2238 from rfl, totK_node, atot2237, atot2238]
  decide +kernel

theorem arows2242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2242 = true := by
  rw [show A10K2.u2242 = KTree.node A10K2.u2240 (nat_lit 39817286) (nat_lit 14595535263) (nat_lit 0) A10K2.u2241 from rfl, allE_node, arows2240, irow2242, arows2241]
  all_goals rfl

theorem atot2242 : totK PA10K2 A10K2.u2242 = [0, 0, 1631683727928, 6511163519064, 8133301481644, 3319561354834, 346049240616, 6318667960, 0, 0] := by
  rw [show A10K2.u2242 = KTree.node A10K2.u2240 (nat_lit 39817286) (nat_lit 14595535263) (nat_lit 0) A10K2.u2241 from rfl, totK_node, atot2240, atot2241]
  decide +kernel

theorem arows2246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2246 = true := by
  rw [show A10K2.u2246 = KTree.node A10K2.u2244 (nat_lit 39839218) (nat_lit 14258420018) (nat_lit 0) A10K2.u2245 from rfl, allE_node, arows2244, irow2246, arows2245]
  all_goals rfl

theorem atot2246 : totK PA10K2 A10K2.u2246 = [0, 0, 867755375247, 4801971212474, 8263567365189, 4846514491387, 738437961821, 18571798697, 0, 0] := by
  rw [show A10K2.u2246 = KTree.node A10K2.u2244 (nat_lit 39839218) (nat_lit 14258420018) (nat_lit 0) A10K2.u2245 from rfl, totK_node, atot2244, atot2245]
  decide +kernel

theorem arows2249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2249 = true := by
  rw [show A10K2.u2249 = KTree.node A10K2.u2247 (nat_lit 40447382) (nat_lit 15972102701) (nat_lit 0) A10K2.u2248 from rfl, allE_node, arows2247, irow2249, arows2248]
  all_goals rfl

theorem atot2249 : totK PA10K2 A10K2.u2249 = [0, 1021347070404, 4411275118690, 6735215901952, 4704416047866, 1985964596906, 553781162399, 48886019071, 0, 0] := by
  rw [show A10K2.u2249 = KTree.node A10K2.u2247 (nat_lit 40447382) (nat_lit 15972102701) (nat_lit 0) A10K2.u2248 from rfl, totK_node, atot2247, atot2248]
  decide +kernel

theorem arows2254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2254 = true := by
  rw [show A10K2.u2254 = KTree.node A10K2.u2252 (nat_lit 40458460) (nat_lit 11107961971) (nat_lit 0) A10K2.u2253 from rfl, allE_node, arows2252, irow2254, arows2253]
  all_goals rfl

theorem atot2254 : totK PA10K2 A10K2.u2254 = [0, 1359421431257, 5961722845216, 8145205234923, 3447499000188, 355473909827, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2254 = KTree.node A10K2.u2252 (nat_lit 40458460) (nat_lit 11107961971) (nat_lit 0) A10K2.u2253 from rfl, totK_node, atot2252, atot2253]
  decide +kernel

theorem arows2257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2257 = true := by
  rw [show A10K2.u2257 = KTree.node A10K2.u2255 (nat_lit 40478500) (nat_lit 13734798012) (nat_lit 0) A10K2.u2256 from rfl, allE_node, arows2255, irow2257, arows2256]
  all_goals rfl

theorem atot2257 : totK PA10K2 A10K2.u2257 = [0, 0, 1588167609379, 6380055884707, 7937184470818, 3213603786442, 472397531035, 25565504801, 0, 0] := by
  rw [show A10K2.u2257 = KTree.node A10K2.u2255 (nat_lit 40478500) (nat_lit 13734798012) (nat_lit 0) A10K2.u2256 from rfl, totK_node, atot2255, atot2256]
  decide +kernel

theorem arows2261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2261 = true := by
  rw [show A10K2.u2261 = KTree.node A10K2.u2259 (nat_lit 40487745) (nat_lit 5318470600) (nat_lit 0) A10K2.u2260 from rfl, allE_node, arows2259, irow2261, arows2260]
  all_goals rfl

theorem atot2261 : totK PA10K2 A10K2.u2261 = [0, 0, 1276166830741, 5603486406432, 7895663967597, 3587857307646, 456665062862, 11638555097, 0, 0] := by
  rw [show A10K2.u2261 = KTree.node A10K2.u2259 (nat_lit 40487745) (nat_lit 5318470600) (nat_lit 0) A10K2.u2260 from rfl, totK_node, atot2259, atot2260]
  decide +kernel

theorem arows2264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2264 = true := by
  rw [show A10K2.u2264 = KTree.node A10K2.u2262 (nat_lit 40508051) (nat_lit 10609682990) (nat_lit 0) A10K2.u2263 from rfl, allE_node, arows2262, irow2264, arows2263]
  all_goals rfl

theorem atot2264 : totK PA10K2 A10K2.u2264 = [0, 1227264424580, 5385452579424, 7693862870517, 4030695711488, 837999446098, 47238528649, 0, 0, 0] := by
  rw [show A10K2.u2264 = KTree.node A10K2.u2262 (nat_lit 40508051) (nat_lit 10609682990) (nat_lit 0) A10K2.u2263 from rfl, totK_node, atot2262, atot2263]
  decide +kernel

theorem arows2270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2270 = true := by
  rw [show A10K2.u2270 = KTree.node A10K2.u2268 (nat_lit 40519410) (nat_lit 14566784681) (nat_lit 0) A10K2.u2269 from rfl, allE_node, arows2268, irow2270, arows2269]
  all_goals rfl

theorem atot2270 : totK PA10K2 A10K2.u2270 = [0, 773611290687, 4278656032683, 7760968424035, 4921412586947, 902047599431, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u2270 = KTree.node A10K2.u2268 (nat_lit 40519410) (nat_lit 14566784681) (nat_lit 0) A10K2.u2269 from rfl, totK_node, atot2268, atot2269]
  decide +kernel

theorem arows2273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2273 = true := by
  rw [show A10K2.u2273 = KTree.node A10K2.u2271 (nat_lit 40545754) (nat_lit 14491231619) (nat_lit 0) A10K2.u2272 from rfl, allE_node, arows2271, irow2273, arows2272]
  all_goals rfl

theorem atot2273 : totK PA10K2 A10K2.u2273 = [0, 0, 1825940669264, 7072561251951, 7738859581999, 2028808538647, 100206146311, 0, 0, 0] := by
  rw [show A10K2.u2273 = KTree.node A10K2.u2271 (nat_lit 40545754) (nat_lit 14491231619) (nat_lit 0) A10K2.u2272 from rfl, totK_node, atot2271, atot2272]
  decide +kernel

theorem arows2277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2277 = true := by
  rw [show A10K2.u2277 = KTree.node A10K2.u2275 (nat_lit 40571511) (nat_lit 9683225989) (nat_lit 0) A10K2.u2276 from rfl, allE_node, arows2275, irow2277, arows2276]
  all_goals rfl

theorem atot2277 : totK PA10K2 A10K2.u2277 = [0, 1292819454161, 5226237782701, 7213510870112, 4452412013044, 1438801542916, 203667120553, 6354482628, 0, 0] := by
  rw [show A10K2.u2277 = KTree.node A10K2.u2275 (nat_lit 40571511) (nat_lit 9683225989) (nat_lit 0) A10K2.u2276 from rfl, totK_node, atot2275, atot2276]
  decide +kernel

theorem arows2280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2280 = true := by
  rw [show A10K2.u2280 = KTree.node A10K2.u2278 (nat_lit 40592789) (nat_lit 4777374898) (nat_lit 0) A10K2.u2279 from rfl, allE_node, arows2278, irow2280, arows2279]
  all_goals rfl

theorem atot2280 : totK PA10K2 A10K2.u2280 = [0, 836871677580, 4403548397630, 8021845065186, 5461973647458, 1090007116330, 45296925298, 0, 0, 0] := by
  rw [show A10K2.u2280 = KTree.node A10K2.u2278 (nat_lit 40592789) (nat_lit 4777374898) (nat_lit 0) A10K2.u2279 from rfl, totK_node, atot2278, atot2279]
  decide +kernel

theorem arows2285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2285 = true := by
  rw [show A10K2.u2285 = KTree.node A10K2.u2283 (nat_lit 40607105) (nat_lit 9576390322) (nat_lit 0) A10K2.u2284 from rfl, allE_node, arows2283, irow2285, arows2284]
  all_goals rfl

theorem atot2285 : totK PA10K2 A10K2.u2285 = [0, 0, 1614164429993, 6588426350233, 8328383431037, 3256733213450, 259818634411, 0, 0, 0] := by
  rw [show A10K2.u2285 = KTree.node A10K2.u2283 (nat_lit 40607105) (nat_lit 9576390322) (nat_lit 0) A10K2.u2284 from rfl, totK_node, atot2283, atot2284]
  decide +kernel

theorem arows2288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2288 = true := by
  rw [show A10K2.u2288 = KTree.node A10K2.u2286 (nat_lit 40627412) (nat_lit 9142971354) (nat_lit 0) A10K2.u2287 from rfl, allE_node, arows2286, irow2288, arows2287]
  all_goals rfl

theorem atot2288 : totK PA10K2 A10K2.u2288 = [0, 0, 836160940386, 4501253784085, 8080119487650, 5343257645040, 1005306208295, 24696255293, 0, 0] := by
  rw [show A10K2.u2288 = KTree.node A10K2.u2286 (nat_lit 40627412) (nat_lit 9142971354) (nat_lit 0) A10K2.u2287 from rfl, totK_node, atot2286, atot2287]
  decide +kernel

theorem arows2292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2292 = true := by
  rw [show A10K2.u2292 = KTree.node A10K2.u2290 (nat_lit 40711525) (nat_lit 7099444323) (nat_lit 0) A10K2.u2291 from rfl, allE_node, arows2290, irow2292, arows2291]
  all_goals rfl

theorem atot2292 : totK PA10K2 A10K2.u2292 = [0, 0, 1307994650460, 5547278182833, 7642252872076, 3942066376737, 738171893031, 55249814038, 0, 0] := by
  rw [show A10K2.u2292 = KTree.node A10K2.u2290 (nat_lit 40711525) (nat_lit 7099444323) (nat_lit 0) A10K2.u2291 from rfl, totK_node, atot2290, atot2291]
  decide +kernel

theorem arows2295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2295 = true := by
  rw [show A10K2.u2295 = KTree.node A10K2.u2293 (nat_lit 40723697) (nat_lit 5154490606) (nat_lit 0) A10K2.u2294 from rfl, allE_node, arows2293, irow2295, arows2294]
  all_goals rfl

theorem atot2295 : totK PA10K2 A10K2.u2295 = [0, 0, 1056203050991, 5212092355204, 8258261306566, 4202536306619, 563201910580, 13202416085, 0, 0] := by
  rw [show A10K2.u2295 = KTree.node A10K2.u2293 (nat_lit 40723697) (nat_lit 5154490606) (nat_lit 0) A10K2.u2294 from rfl, totK_node, atot2293, atot2294]
  decide +kernel

theorem arows2304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2304 = true := by
  rw [show A10K2.u2304 = KTree.node A10K2.u2302 (nat_lit 40742833) (nat_lit 6437184825) (nat_lit 0) A10K2.u2303 from rfl, allE_node, arows2302, irow2304, arows2303]
  all_goals rfl

theorem atot2304 : totK PA10K2 A10K2.u2304 = [0, 0, 0, 1408880781391, 5782298428371, 7484898739891, 3550318523220, 619701190211, 31018567651, 0] := by
  rw [show A10K2.u2304 = KTree.node A10K2.u2302 (nat_lit 40742833) (nat_lit 6437184825) (nat_lit 0) A10K2.u2303 from rfl, totK_node, atot2302, atot2303]
  decide +kernel

theorem arows2307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2307 = true := by
  rw [show A10K2.u2307 = KTree.node A10K2.u2305 (nat_lit 40756446) (nat_lit 11389925001) (nat_lit 0) A10K2.u2306 from rfl, allE_node, arows2305, irow2307, arows2306]
  all_goals rfl

theorem atot2307 : totK PA10K2 A10K2.u2307 = [0, 0, 424355675811, 2742898033890, 6369412047209, 6467354654503, 2391310833607, 268873873207, 5685526223, 0] := by
  rw [show A10K2.u2307 = KTree.node A10K2.u2305 (nat_lit 40756446) (nat_lit 11389925001) (nat_lit 0) A10K2.u2306 from rfl, totK_node, atot2305, atot2306]
  decide +kernel

theorem arows2311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2311 = true := by
  rw [show A10K2.u2311 = KTree.node A10K2.u2309 (nat_lit 40775572) (nat_lit 8113384784) (nat_lit 0) A10K2.u2310 from rfl, allE_node, arows2309, irow2311, arows2310]
  all_goals rfl

theorem atot2311 : totK PA10K2 A10K2.u2311 = [0, 0, 1103138122028, 4915414152414, 7692267115701, 4376635661492, 758641199314, 37229241746, 0, 0] := by
  rw [show A10K2.u2311 = KTree.node A10K2.u2309 (nat_lit 40775572) (nat_lit 8113384784) (nat_lit 0) A10K2.u2310 from rfl, totK_node, atot2309, atot2310]
  decide +kernel

theorem arows2314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2314 = true := by
  rw [show A10K2.u2314 = KTree.node A10K2.u2312 (nat_lit 40786615) (nat_lit 5664032737) (nat_lit 0) A10K2.u2313 from rfl, allE_node, arows2312, irow2314, arows2313]
  all_goals rfl

theorem atot2314 : totK PA10K2 A10K2.u2314 = [0, 0, 467092711113, 3711004435774, 7947300571236, 5423685960162, 976099751602, 44833411993, 0, 0] := by
  rw [show A10K2.u2314 = KTree.node A10K2.u2312 (nat_lit 40786615) (nat_lit 5664032737) (nat_lit 0) A10K2.u2313 from rfl, totK_node, atot2312, atot2313]
  decide +kernel

theorem arows2319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2319 = true := by
  rw [show A10K2.u2319 = KTree.node A10K2.u2317 (nat_lit 40817836) (nat_lit 12583817227) (nat_lit 0) A10K2.u2318 from rfl, allE_node, arows2317, irow2319, arows2318]
  all_goals rfl

theorem atot2319 : totK PA10K2 A10K2.u2319 = [0, 0, 786796184452, 3383794453637, 6380264978256, 6148204914600, 2065584079225, 232102582031, 5982052406, 0] := by
  rw [show A10K2.u2319 = KTree.node A10K2.u2317 (nat_lit 40817836) (nat_lit 12583817227) (nat_lit 0) A10K2.u2318 from rfl, totK_node, atot2317, atot2318]
  decide +kernel

theorem arows2322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2322 = true := by
  rw [show A10K2.u2322 = KTree.node A10K2.u2320 (nat_lit 40843620) (nat_lit 13851847377) (nat_lit 0) A10K2.u2321 from rfl, allE_node, arows2320, irow2322, arows2321]
  all_goals rfl

theorem atot2322 : totK PA10K2 A10K2.u2322 = [0, 0, 1334840535497, 5871327220423, 8260837345889, 3827792556356, 535044544488, 25660650750, 0, 0] := by
  rw [show A10K2.u2322 = KTree.node A10K2.u2320 (nat_lit 40843620) (nat_lit 13851847377) (nat_lit 0) A10K2.u2321 from rfl, totK_node, atot2320, atot2321]
  decide +kernel

theorem arows2326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2326 = true := by
  rw [show A10K2.u2326 = KTree.node A10K2.u2324 (nat_lit 40896624) (nat_lit 14778862249) (nat_lit 0) A10K2.u2325 from rfl, allE_node, arows2324, irow2326, arows2325]
  all_goals rfl

theorem atot2326 : totK PA10K2 A10K2.u2326 = [0, 818400366434, 3474031733540, 5908404464541, 5464263545866, 3002063024446, 704579596034, 41590655314, 0, 0] := by
  rw [show A10K2.u2326 = KTree.node A10K2.u2324 (nat_lit 40896624) (nat_lit 14778862249) (nat_lit 0) A10K2.u2325 from rfl, totK_node, atot2324, atot2325]
  decide +kernel

theorem arows2329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2329 = true := by
  rw [show A10K2.u2329 = KTree.node A10K2.u2327 (nat_lit 40917861) (nat_lit 7244284449) (nat_lit 0) A10K2.u2328 from rfl, allE_node, arows2327, irow2329, arows2328]
  all_goals rfl

theorem atot2329 : totK PA10K2 A10K2.u2329 = [0, 481398847354, 3572516704496, 7752560362910, 5809300063096, 1259464390097, 68756073609, 0, 0, 0] := by
  rw [show A10K2.u2329 = KTree.node A10K2.u2327 (nat_lit 40917861) (nat_lit 7244284449) (nat_lit 0) A10K2.u2328 from rfl, totK_node, atot2327, atot2328]
  decide +kernel

theorem arows2335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2335 = true := by
  rw [show A10K2.u2335 = KTree.node A10K2.u2333 (nat_lit 40970081) (nat_lit 4904130694) (nat_lit 0) A10K2.u2334 from rfl, allE_node, arows2333, irow2335, arows2334]
  all_goals rfl

theorem atot2335 : totK PA10K2 A10K2.u2335 = [0, 844157640669, 3877870952235, 6731003440324, 5526178636901, 1881763217356, 217612670675, 5546304973, 0, 0] := by
  rw [show A10K2.u2335 = KTree.node A10K2.u2333 (nat_lit 40970081) (nat_lit 4904130694) (nat_lit 0) A10K2.u2334 from rfl, totK_node, atot2333, atot2334]
  decide +kernel

theorem arows2338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2338 = true := by
  rw [show A10K2.u2338 = KTree.node A10K2.u2336 (nat_lit 40979114) (nat_lit 12693000693) (nat_lit 0) A10K2.u2337 from rfl, allE_node, arows2336, irow2338, arows2337]
  all_goals rfl

theorem atot2338 : totK PA10K2 A10K2.u2338 = [0, 1307107705811, 5471335597997, 7829578494866, 3976748356679, 558051838622, 12388698189, 0, 0, 0] := by
  rw [show A10K2.u2338 = KTree.node A10K2.u2336 (nat_lit 40979114) (nat_lit 12693000693) (nat_lit 0) A10K2.u2337 from rfl, totK_node, atot2336, atot2337]
  decide +kernel

theorem arows2342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2342 = true := by
  rw [show A10K2.u2342 = KTree.node A10K2.u2340 (nat_lit 41002722) (nat_lit 13752822675) (nat_lit 0) A10K2.u2341 from rfl, allE_node, arows2340, irow2342, arows2341]
  all_goals rfl

theorem atot2342 : totK PA10K2 A10K2.u2342 = [0, 45544482702, 1940127810733, 6705841001786, 7534729211080, 2969762346814, 455814416791, 25565504801, 0, 0] := by
  rw [show A10K2.u2342 = KTree.node A10K2.u2340 (nat_lit 41002722) (nat_lit 13752822675) (nat_lit 0) A10K2.u2341 from rfl, totK_node, atot2340, atot2341]
  decide +kernel

theorem arows2345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2345 = true := by
  rw [show A10K2.u2345 = KTree.node A10K2.u2343 (nat_lit 41011977) (nat_lit 8274386621) (nat_lit 0) A10K2.u2344 from rfl, allE_node, arows2343, irow2345, arows2344]
  all_goals rfl

theorem atot2345 : totK PA10K2 A10K2.u2345 = [0, 0, 1350151801071, 5700722436726, 7850737018942, 3603971754756, 456346998590, 11638555097, 0, 0] := by
  rw [show A10K2.u2345 = KTree.node A10K2.u2343 (nat_lit 41011977) (nat_lit 8274386621) (nat_lit 0) A10K2.u2344 from rfl, totK_node, atot2343, atot2344]
  decide +kernel

theorem arows2350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2350 = true := by
  rw [show A10K2.u2350 = KTree.node A10K2.u2348 (nat_lit 41030500) (nat_lit 12922967299) (nat_lit 0) A10K2.u2349 from rfl, allE_node, arows2348, irow2350, arows2349]
  all_goals rfl

theorem atot2350 : totK PA10K2 A10K2.u2350 = [0, 1352019964063, 5383688198340, 7237635439681, 4028231837201, 979494537292, 66170415904, 0, 0, 0] := by
  rw [show A10K2.u2350 = KTree.node A10K2.u2348 (nat_lit 41030500) (nat_lit 12922967299) (nat_lit 0) A10K2.u2349 from rfl, totK_node, atot2348, atot2349]
  decide +kernel

theorem arows2353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2353 = true := by
  rw [show A10K2.u2353 = KTree.node A10K2.u2351 (nat_lit 41042796) (nat_lit 11348012497) (nat_lit 0) A10K2.u2352 from rfl, allE_node, arows2351, irow2353, arows2352]
  all_goals rfl

theorem atot2353 : totK PA10K2 A10K2.u2353 = [0, 822103226267, 4602449028635, 7976765830836, 4677021981146, 774187307207, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2353 = KTree.node A10K2.u2351 (nat_lit 41042796) (nat_lit 11348012497) (nat_lit 0) A10K2.u2352 from rfl, totK_node, atot2351, atot2352]
  decide +kernel

theorem arows2357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2357 = true := by
  rw [show A10K2.u2357 = KTree.node A10K2.u2355 (nat_lit 41068356) (nat_lit 11968512074) (nat_lit 0) A10K2.u2356 from rfl, allE_node, arows2355, irow2357, arows2356]
  all_goals rfl

theorem atot2357 : totK PA10K2 A10K2.u2357 = [0, 0, 1934772379703, 7252367618875, 7528567031132, 1983559762852, 121620573140, 0, 0, 0] := by
  rw [show A10K2.u2357 = KTree.node A10K2.u2355 (nat_lit 41068356) (nat_lit 11968512074) (nat_lit 0) A10K2.u2356 from rfl, totK_node, atot2355, atot2356]
  decide +kernel

theorem arows2360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2360 = true := by
  rw [show A10K2.u2360 = KTree.node A10K2.u2358 (nat_lit 41157105) (nat_lit 8771603586) (nat_lit 0) A10K2.u2359 from rfl, allE_node, arows2358, irow2360, arows2359]
  all_goals rfl

theorem atot2360 : totK PA10K2 A10K2.u2360 = [0, 0, 1107954552056, 5347179574237, 7982757697689, 3684811339291, 510406855508, 11801668502, 0, 0] := by
  rw [show A10K2.u2360 = KTree.node A10K2.u2358 (nat_lit 41157105) (nat_lit 8771603586) (nat_lit 0) A10K2.u2359 from rfl, totK_node, atot2358, atot2359]
  decide +kernel

theorem arows2367 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2367 = true := by
  rw [show A10K2.u2367 = KTree.node A10K2.u2365 (nat_lit 41179937) (nat_lit 9273335518) (nat_lit 0) A10K2.u2366 from rfl, allE_node, arows2365, irow2367, arows2366]
  all_goals rfl

theorem atot2367 : totK PA10K2 A10K2.u2367 = [0, 0, 1339206046865, 5894547121962, 8166632889717, 3293714416991, 314535499549, 6354482628, 0, 0] := by
  rw [show A10K2.u2367 = KTree.node A10K2.u2365 (nat_lit 41179937) (nat_lit 9273335518) (nat_lit 0) A10K2.u2366 from rfl, totK_node, atot2365, atot2366]
  decide +kernel

theorem arows2370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2370 = true := by
  rw [show A10K2.u2370 = KTree.node A10K2.u2368 (nat_lit 41240324) (nat_lit 12856571978) (nat_lit 0) A10K2.u2369 from rfl, allE_node, arows2368, irow2370, arows2369]
  all_goals rfl

theorem atot2370 : totK PA10K2 A10K2.u2370 = [0, 0, 1059181212158, 4812414208160, 7634744094225, 4497869162277, 802306204546, 37807056478, 0, 0] := by
  rw [show A10K2.u2370 = KTree.node A10K2.u2368 (nat_lit 41240324) (nat_lit 12856571978) (nat_lit 0) A10K2.u2369 from rfl, totK_node, atot2368, atot2369]
  decide +kernel

theorem arows2374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2374 = true := by
  rw [show A10K2.u2374 = KTree.node A10K2.u2372 (nat_lit 41288193) (nat_lit 10582213929) (nat_lit 0) A10K2.u2373 from rfl, allE_node, arows2372, irow2374, arows2373]
  all_goals rfl

theorem atot2374 : totK PA10K2 A10K2.u2374 = [0, 0, 1175105952981, 5493369917673, 8192038011089, 3914246120982, 518861582411, 12423235244, 0, 0] := by
  rw [show A10K2.u2374 = KTree.node A10K2.u2372 (nat_lit 41288193) (nat_lit 10582213929) (nat_lit 0) A10K2.u2373 from rfl, totK_node, atot2372, atot2373]
  decide +kernel

theorem arows2377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2377 = true := by
  rw [show A10K2.u2377 = KTree.node A10K2.u2375 (nat_lit 41302263) (nat_lit 6637669874) (nat_lit 0) A10K2.u2376 from rfl, allE_node, arows2375, irow2377, arows2376]
  all_goals rfl

theorem atot2377 : totK PA10K2 A10K2.u2377 = [0, 0, 1289878713683, 5573704697466, 7729431746935, 3686610171703, 572495965339, 31003444686, 0, 0] := by
  rw [show A10K2.u2377 = KTree.node A10K2.u2375 (nat_lit 41302263) (nat_lit 6637669874) (nat_lit 0) A10K2.u2376 from rfl, totK_node, atot2375, atot2376]
  decide +kernel

theorem arows2382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2382 = true := by
  rw [show A10K2.u2382 = KTree.node A10K2.u2380 (nat_lit 41322775) (nat_lit 3350017608) (nat_lit 0) A10K2.u2381 from rfl, allE_node, arows2380, irow2382, arows2381]
  all_goals rfl

theorem atot2382 : totK PA10K2 A10K2.u2382 = [0, 0, 0, 2617661384204, 8250427479433, 6293846059237, 1170180113569, 49785862777, 0, 0] := by
  rw [show A10K2.u2382 = KTree.node A10K2.u2380 (nat_lit 41322775) (nat_lit 3350017608) (nat_lit 0) A10K2.u2381 from rfl, totK_node, atot2380, atot2381]
  decide +kernel

theorem arows2385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2385 = true := by
  rw [show A10K2.u2385 = KTree.node A10K2.u2383 (nat_lit 41343329) (nat_lit 8845514092) (nat_lit 0) A10K2.u2384 from rfl, allE_node, arows2383, irow2385, arows2384]
  all_goals rfl

theorem atot2385 : totK PA10K2 A10K2.u2385 = [0, 591294713498, 2465630538831, 4081891165876, 4835000182754, 4740216957018, 1933478236648, 252403368887, 6354482628, 0] := by
  rw [show A10K2.u2385 = KTree.node A10K2.u2383 (nat_lit 41343329) (nat_lit 8845514092) (nat_lit 0) A10K2.u2384 from rfl, totK_node, atot2383, atot2384]
  decide +kernel

theorem arows2389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2389 = true := by
  rw [show A10K2.u2389 = KTree.node A10K2.u2387 (nat_lit 41447481) (nat_lit 7321262860) (nat_lit 0) A10K2.u2388 from rfl, allE_node, arows2387, irow2389, arows2388]
  all_goals rfl

theorem atot2389 : totK PA10K2 A10K2.u2389 = [0, 794133235012, 4305440917668, 7987337598551, 5838243051191, 1394656396733, 82984143167, 0, 0, 0] := by
  rw [show A10K2.u2389 = KTree.node A10K2.u2387 (nat_lit 41447481) (nat_lit 7321262860) (nat_lit 0) A10K2.u2388 from rfl, totK_node, atot2387, atot2388]
  decide +kernel

theorem arows2392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2392 = true := by
  rw [show A10K2.u2392 = KTree.node A10K2.u2390 (nat_lit 41477311) (nat_lit 13932637566) (nat_lit 0) A10K2.u2391 from rfl, allE_node, arows2390, irow2392, arows2391]
  all_goals rfl

theorem atot2392 : totK PA10K2 A10K2.u2392 = [0, 548589231577, 2980741276570, 6469339302724, 6807099512456, 2844404045954, 355620167718, 7237400819, 0, 0] := by
  rw [show A10K2.u2392 = KTree.node A10K2.u2390 (nat_lit 41477311) (nat_lit 13932637566) (nat_lit 0) A10K2.u2391 from rfl, totK_node, atot2390, atot2391]
  decide +kernel

theorem arows2398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2398 = true := by
  rw [show A10K2.u2398 = KTree.node A10K2.u2396 (nat_lit 41499888) (nat_lit 10486906893) (nat_lit 0) A10K2.u2397 from rfl, allE_node, arows2396, irow2398, arows2397]
  all_goals rfl

theorem atot2398 : totK PA10K2 A10K2.u2398 = [0, 851292349273, 4617629694020, 8158376956688, 4874995872841, 787233827878, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2398 = KTree.node A10K2.u2396 (nat_lit 41499888) (nat_lit 10486906893) (nat_lit 0) A10K2.u2397 from rfl, totK_node, atot2396, atot2397]
  decide +kernel

theorem arows2401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2401 = true := by
  rw [show A10K2.u2401 = KTree.node A10K2.u2399 (nat_lit 41513586) (nat_lit 7792494334) (nat_lit 0) A10K2.u2400 from rfl, allE_node, arows2399, irow2401, arows2400]
  all_goals rfl

theorem atot2401 : totK PA10K2 A10K2.u2401 = [0, 815136327260, 4235486949214, 7692460421321, 5752160896595, 1515726502839, 95173279525, 0, 0, 0] := by
  rw [show A10K2.u2401 = KTree.node A10K2.u2399 (nat_lit 41513586) (nat_lit 7792494334) (nat_lit 0) A10K2.u2400 from rfl, totK_node, atot2399, atot2400]
  decide +kernel

theorem arows2405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2405 = true := by
  rw [show A10K2.u2405 = KTree.node A10K2.u2403 (nat_lit 41532192) (nat_lit 9889356483) (nat_lit 0) A10K2.u2404 from rfl, allE_node, arows2403, irow2405, arows2404]
  all_goals rfl

theorem atot2405 : totK PA10K2 A10K2.u2405 = [0, 0, 975187145475, 5145612267800, 8110654673362, 4136093150446, 667612947008, 31082886609, 0, 0] := by
  rw [show A10K2.u2405 = KTree.node A10K2.u2403 (nat_lit 41532192) (nat_lit 9889356483) (nat_lit 0) A10K2.u2404 from rfl, totK_node, atot2403, atot2404]
  decide +kernel

theorem arows2408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2408 = true := by
  rw [show A10K2.u2408 = KTree.node A10K2.u2406 (nat_lit 41615625) (nat_lit 9792185400) (nat_lit 0) A10K2.u2407 from rfl, allE_node, arows2406, irow2408, arows2407]
  all_goals rfl

theorem atot2408 : totK PA10K2 A10K2.u2408 = [0, 625736493037, 3743267287260, 7449585762626, 5969538416512, 1990136235861, 224488119521, 5885702948, 0, 0] := by
  rw [show A10K2.u2408 = KTree.node A10K2.u2406 (nat_lit 41615625) (nat_lit 9792185400) (nat_lit 0) A10K2.u2407 from rfl, totK_node, atot2406, atot2407]
  decide +kernel

theorem arows2413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2413 = true := by
  rw [show A10K2.u2413 = KTree.node A10K2.u2411 (nat_lit 41629176) (nat_lit 10469563503) (nat_lit 0) A10K2.u2412 from rfl, allE_node, arows2411, irow2413, arows2412]
  all_goals rfl

theorem atot2413 : totK PA10K2 A10K2.u2413 = [0, 1327180675402, 5611398189038, 7859504052860, 4145773105331, 707401002355, 31452269383, 0, 0, 0] := by
  rw [show A10K2.u2413 = KTree.node A10K2.u2411 (nat_lit 41629176) (nat_lit 10469563503) (nat_lit 0) A10K2.u2412 from rfl, totK_node, atot2411, atot2412]
  decide +kernel

theorem arows2416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2416 = true := by
  rw [show A10K2.u2416 = KTree.node A10K2.u2414 (nat_lit 41647496) (nat_lit 13778730677) (nat_lit 0) A10K2.u2415 from rfl, allE_node, arows2414, irow2416, arows2415]
  all_goals rfl

theorem atot2416 : totK PA10K2 A10K2.u2416 = [0, 330865856800, 2755533588140, 7308954650034, 7236399124720, 2268500235884, 145396426964, 0, 0, 0] := by
  rw [show A10K2.u2416 = KTree.node A10K2.u2414 (nat_lit 41647496) (nat_lit 13778730677) (nat_lit 0) A10K2.u2415 from rfl, totK_node, atot2414, atot2415]
  decide +kernel

theorem arows2420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2420 = true := by
  rw [show A10K2.u2420 = KTree.node A10K2.u2418 (nat_lit 41660089) (nat_lit 5554587333) (nat_lit 0) A10K2.u2419 from rfl, allE_node, arows2418, irow2420, arows2419]
  all_goals rfl

theorem atot2420 : totK PA10K2 A10K2.u2420 = [0, 0, 1325725644847, 5686150190851, 7991175266009, 4114151484159, 583142023274, 13679205470, 0, 0] := by
  rw [show A10K2.u2420 = KTree.node A10K2.u2418 (nat_lit 41660089) (nat_lit 5554587333) (nat_lit 0) A10K2.u2419 from rfl, totK_node, atot2418, atot2419]
  decide +kernel

theorem arows2423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2423 = true := by
  rw [show A10K2.u2423 = KTree.node A10K2.u2421 (nat_lit 41679916) (nat_lit 4412449162) (nat_lit 0) A10K2.u2422 from rfl, allE_node, arows2421, irow2423, arows2422]
  all_goals rfl

theorem atot2423 : totK PA10K2 A10K2.u2423 = [796021182214, 2610860683949, 2771545684918, 2999643068828, 5303008610527, 4084248818578, 979638778335, 61110126106, 0, 0] := by
  rw [show A10K2.u2423 = KTree.node A10K2.u2421 (nat_lit 41679916) (nat_lit 4412449162) (nat_lit 0) A10K2.u2422 from rfl, totK_node, atot2421, atot2422]
  decide +kernel

theorem arows2431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2431 = true := by
  rw [show A10K2.u2431 = KTree.node A10K2.u2429 (nat_lit 41959808) (nat_lit 15396112663) (nat_lit 0) A10K2.u2430 from rfl, allE_node, arows2429, irow2431, arows2430]
  all_goals rfl

theorem atot2431 : totK PA10K2 A10K2.u2431 = [790384174615, 4637917807735, 8196035076371, 4665607621364, 745602439525, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2431 = KTree.node A10K2.u2429 (nat_lit 41959808) (nat_lit 15396112663) (nat_lit 0) A10K2.u2430 from rfl, totK_node, atot2429, atot2430]
  decide +kernel

theorem arows2434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2434 = true := by
  rw [show A10K2.u2434 = KTree.node A10K2.u2432 (nat_lit 41972343) (nat_lit 10187013203) (nat_lit 0) A10K2.u2433 from rfl, allE_node, arows2432, irow2434, arows2433]
  all_goals rfl

theorem atot2434 : totK PA10K2 A10K2.u2434 = [593902697676, 3609200962576, 7691879258847, 6286616311094, 1556284123203, 93477475948, 0, 0, 0, 0] := by
  rw [show A10K2.u2434 = KTree.node A10K2.u2432 (nat_lit 41972343) (nat_lit 10187013203) (nat_lit 0) A10K2.u2433 from rfl, totK_node, atot2432, atot2433]
  decide +kernel

theorem arows2438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2438 = true := by
  rw [show A10K2.u2438 = KTree.node A10K2.u2436 (nat_lit 41992588) (nat_lit 8909135796) (nat_lit 0) A10K2.u2437 from rfl, allE_node, arows2436, irow2438, arows2437]
  all_goals rfl

theorem atot2438 : totK PA10K2 A10K2.u2438 = [0, 853661126485, 4827418759599, 8191381049985, 4256152702382, 659051635155, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2438 = KTree.node A10K2.u2436 (nat_lit 41992588) (nat_lit 8909135796) (nat_lit 0) A10K2.u2437 from rfl, totK_node, atot2436, atot2437]
  decide +kernel

theorem arows2441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2441 = true := by
  rw [show A10K2.u2441 = KTree.node A10K2.u2439 (nat_lit 42076192) (nat_lit 13959179896) (nat_lit 0) A10K2.u2440 from rfl, allE_node, arows2439, irow2441, arows2440]
  all_goals rfl

theorem atot2441 : totK PA10K2 A10K2.u2441 = [767063984985, 3962767044242, 7263537466586, 5529145771832, 1743623410486, 217335945706, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u2441 = KTree.node A10K2.u2439 (nat_lit 42076192) (nat_lit 13959179896) (nat_lit 0) A10K2.u2440 from rfl, totK_node, atot2439, atot2440]
  decide +kernel

theorem arows2446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2446 = true := by
  rw [show A10K2.u2446 = KTree.node A10K2.u2444 (nat_lit 42088611) (nat_lit 10499862237) (nat_lit 0) A10K2.u2445 from rfl, allE_node, arows2444, irow2446, arows2445]
  all_goals rfl

theorem atot2446 : totK PA10K2 A10K2.u2446 = [1380631111097, 5729562764194, 7601615604229, 3754205020400, 701431624651, 37229241746, 0, 0, 0, 0] := by
  rw [show A10K2.u2446 = KTree.node A10K2.u2444 (nat_lit 42088611) (nat_lit 10499862237) (nat_lit 0) A10K2.u2445 from rfl, totK_node, atot2444, atot2445]
  decide +kernel

theorem arows2449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2449 = true := by
  rw [show A10K2.u2449 = KTree.node A10K2.u2447 (nat_lit 42109157) (nat_lit 7148711552) (nat_lit 0) A10K2.u2448 from rfl, allE_node, arows2447, irow2449, arows2448]
  all_goals rfl

theorem atot2449 : totK PA10K2 A10K2.u2449 = [0, 2391474276196, 7937513033427, 7101870063857, 1663813081172, 77608611860, 0, 0, 0, 0] := by
  rw [show A10K2.u2449 = KTree.node A10K2.u2447 (nat_lit 42109157) (nat_lit 7148711552) (nat_lit 0) A10K2.u2448 from rfl, totK_node, atot2447, atot2448]
  decide +kernel

theorem arows2453 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2453 = true := by
  rw [show A10K2.u2453 = KTree.node A10K2.u2451 (nat_lit 42129464) (nat_lit 12675437985) (nat_lit 0) A10K2.u2452 from rfl, allE_node, arows2451, irow2453, arows2452]
  all_goals rfl

theorem atot2453 : totK PA10K2 A10K2.u2453 = [0, 1442767486842, 6148684952225, 7927343945717, 2958229625349, 347964181910, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2453 = KTree.node A10K2.u2451 (nat_lit 42129464) (nat_lit 12675437985) (nat_lit 0) A10K2.u2452 from rfl, totK_node, atot2451, atot2452]
  decide +kernel

theorem arows2456 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2456 = true := by
  rw [show A10K2.u2456 = KTree.node A10K2.u2454 (nat_lit 42222153) (nat_lit 9565289491) (nat_lit 0) A10K2.u2455 from rfl, allE_node, arows2454, irow2456, arows2455]
  all_goals rfl

theorem atot2456 : totK PA10K2 A10K2.u2456 = [0, 745005438573, 4420870618206, 8115121596110, 4717901129893, 734334900233, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2456 = KTree.node A10K2.u2454 (nat_lit 42222153) (nat_lit 9565289491) (nat_lit 0) A10K2.u2455 from rfl, totK_node, atot2454, atot2455]
  decide +kernel

theorem arows2462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2462 = true := by
  rw [show A10K2.u2462 = KTree.node A10K2.u2460 (nat_lit 42237170) (nat_lit 13544966476) (nat_lit 0) A10K2.u2461 from rfl, allE_node, arows2460, irow2462, arows2461]
  all_goals rfl

theorem atot2462 : totK PA10K2 A10K2.u2462 = [0, 592958361815, 3602541505121, 7694371241324, 6285672861887, 1503565058571, 78753913629, 0, 0, 0] := by
  rw [show A10K2.u2462 = KTree.node A10K2.u2460 (nat_lit 42237170) (nat_lit 13544966476) (nat_lit 0) A10K2.u2461 from rfl, totK_node, atot2460, atot2461]
  decide +kernel

theorem arows2465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2465 = true := by
  rw [show A10K2.u2465 = KTree.node A10K2.u2463 (nat_lit 42255510) (nat_lit 10397594900) (nat_lit 0) A10K2.u2464 from rfl, allE_node, arows2463, irow2465, arows2464]
  all_goals rfl

theorem atot2465 : totK PA10K2 A10K2.u2465 = [0, 0, 939918899497, 4692794396812, 7638898054021, 4224116587250, 765372887619, 36134558889, 0, 0] := by
  rw [show A10K2.u2465 = KTree.node A10K2.u2463 (nat_lit 42255510) (nat_lit 10397594900) (nat_lit 0) A10K2.u2464 from rfl, totK_node, atot2463, atot2464]
  decide +kernel

theorem arows2469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2469 = true := by
  rw [show A10K2.u2469 = KTree.node A10K2.u2467 (nat_lit 42339116) (nat_lit 13411104735) (nat_lit 0) A10K2.u2468 from rfl, allE_node, arows2467, irow2469, arows2468]
  all_goals rfl

theorem atot2469 : totK PA10K2 A10K2.u2469 = [0, 1015178660875, 4528416438253, 7549009860530, 5220092074784, 1177784251274, 74743123071, 0, 0, 0] := by
  rw [show A10K2.u2469 = KTree.node A10K2.u2467 (nat_lit 42339116) (nat_lit 13411104735) (nat_lit 0) A10K2.u2468 from rfl, totK_node, atot2467, atot2468]
  decide +kernel

theorem arows2472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2472 = true := by
  rw [show A10K2.u2472 = KTree.node A10K2.u2470 (nat_lit 42353185) (nat_lit 10144271537) (nat_lit 0) A10K2.u2471 from rfl, allE_node, arows2470, irow2472, arows2471]
  all_goals rfl

theorem atot2472 : totK PA10K2 A10K2.u2472 = [0, 1131390315437, 5586542720867, 8249284517184, 3598610838393, 372226239764, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u2472 = KTree.node A10K2.u2470 (nat_lit 42353185) (nat_lit 10144271537) (nat_lit 0) A10K2.u2471 from rfl, totK_node, atot2470, atot2471]
  decide +kernel

theorem arows2477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2477 = true := by
  rw [show A10K2.u2477 = KTree.node A10K2.u2475 (nat_lit 42378451) (nat_lit 10878723544) (nat_lit 0) A10K2.u2476 from rfl, allE_node, arows2475, irow2477, arows2476]
  all_goals rfl

theorem atot2477 : totK PA10K2 A10K2.u2477 = [0, 0, 2316896740124, 7750520951396, 7091122601260, 1622087623290, 81783304252, 0, 0, 0] := by
  rw [show A10K2.u2477 = KTree.node A10K2.u2475 (nat_lit 42378451) (nat_lit 10878723544) (nat_lit 0) A10K2.u2476 from rfl, totK_node, atot2475, atot2476]
  decide +kernel

theorem arows2480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2480 = true := by
  rw [show A10K2.u2480 = KTree.node A10K2.u2478 (nat_lit 42543287) (nat_lit 13866747009) (nat_lit 0) A10K2.u2479 from rfl, allE_node, arows2478, irow2480, arows2479]
  all_goals rfl

theorem atot2480 : totK PA10K2 A10K2.u2480 = [860205094993, 3736700297015, 5486513308331, 4186185911704, 3233666657211, 1408329955764, 192289909650, 5676195732, 0, 0] := by
  rw [show A10K2.u2480 = KTree.node A10K2.u2478 (nat_lit 42543287) (nat_lit 13866747009) (nat_lit 0) A10K2.u2479 from rfl, totK_node, atot2478, atot2479]
  decide +kernel

theorem arows2484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2484 = true := by
  rw [show A10K2.u2484 = KTree.node A10K2.u2482 (nat_lit 42553422) (nat_lit 4449224923) (nat_lit 0) A10K2.u2483 from rfl, allE_node, arows2482, irow2484, arows2483]
  all_goals rfl

theorem atot2484 : totK PA10K2 A10K2.u2484 = [1438061005852, 5885497336869, 7829358974103, 3668022232288, 514723530786, 12388698189, 0, 0, 0, 0] := by
  rw [show A10K2.u2484 = KTree.node A10K2.u2482 (nat_lit 42553422) (nat_lit 4449224923) (nat_lit 0) A10K2.u2483 from rfl, totK_node, atot2482, atot2483]
  decide +kernel

theorem arows2487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2487 = true := by
  rw [show A10K2.u2487 = KTree.node A10K2.u2485 (nat_lit 42575315) (nat_lit 10649282280) (nat_lit 0) A10K2.u2486 from rfl, allE_node, arows2485, irow2487, arows2486]
  all_goals rfl

theorem atot2487 : totK PA10K2 A10K2.u2487 = [0, 1925889290900, 6951324404455, 7671151566972, 2930072669949, 435146335403, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2487 = KTree.node A10K2.u2485 (nat_lit 42575315) (nat_lit 10649282280) (nat_lit 0) A10K2.u2486 from rfl, totK_node, atot2485, atot2486]
  decide +kernel

theorem arows2494 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2494 = true := by
  rw [show A10K2.u2494 = KTree.node A10K2.u2492 (nat_lit 42584389) (nat_lit 6961576414) (nat_lit 0) A10K2.u2493 from rfl, allE_node, arows2492, irow2494, arows2493]
  all_goals rfl

theorem atot2494 : totK PA10K2 A10K2.u2494 = [0, 1141482795056, 5386121454233, 8048388215300, 3886161071951, 493699485871, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u2494 = KTree.node A10K2.u2492 (nat_lit 42584389) (nat_lit 6961576414) (nat_lit 0) A10K2.u2493 from rfl, totK_node, atot2492, atot2493]
  decide +kernel

theorem arows2497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2497 = true := by
  rw [show A10K2.u2497 = KTree.node A10K2.u2495 (nat_lit 42603017) (nat_lit 9781991067) (nat_lit 0) A10K2.u2496 from rfl, allE_node, arows2495, irow2497, arows2496]
  all_goals rfl

theorem atot2497 : totK PA10K2 A10K2.u2497 = [1224509320527, 5132530137829, 7308669327540, 4326350045937, 1103363105351, 80484073845, 0, 0, 0, 0] := by
  rw [show A10K2.u2497 = KTree.node A10K2.u2495 (nat_lit 42603017) (nat_lit 9781991067) (nat_lit 0) A10K2.u2496 from rfl, totK_node, atot2495, atot2496]
  decide +kernel

theorem arows2501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2501 = true := by
  rw [show A10K2.u2501 = KTree.node A10K2.u2499 (nat_lit 42615364) (nat_lit 11135578240) (nat_lit 0) A10K2.u2500 from rfl, allE_node, arows2499, irow2501, arows2500]
  all_goals rfl

theorem atot2501 : totK PA10K2 A10K2.u2501 = [876513839775, 4763564032216, 8063437457646, 4651673746209, 761923843825, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2501 = KTree.node A10K2.u2499 (nat_lit 42615364) (nat_lit 11135578240) (nat_lit 0) A10K2.u2500 from rfl, totK_node, atot2499, atot2500]
  decide +kernel

theorem arows2504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2504 = true := by
  rw [show A10K2.u2504 = KTree.node A10K2.u2502 (nat_lit 42641188) (nat_lit 13734798012) (nat_lit 0) A10K2.u2503 from rfl, allE_node, arows2502, irow2504, arows2503]
  all_goals rfl

theorem atot2504 : totK PA10K2 A10K2.u2504 = [0, 2018497788476, 7350374981857, 7484486101982, 1993199943353, 122050191000, 0, 0, 0, 0] := by
  rw [show A10K2.u2504 = KTree.node A10K2.u2502 (nat_lit 42641188) (nat_lit 13734798012) (nat_lit 0) A10K2.u2503 from rfl, totK_node, atot2502, atot2503]
  decide +kernel

theorem arows2509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2509 = true := by
  rw [show A10K2.u2509 = KTree.node A10K2.u2507 (nat_lit 42673609) (nat_lit 4761499622) (nat_lit 0) A10K2.u2508 from rfl, allE_node, arows2507, irow2509, arows2508]
  all_goals rfl

theorem atot2509 : totK PA10K2 A10K2.u2509 = [811248297904, 3696739228133, 6551597256753, 5826220932117, 2230224899164, 297392156758, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2509 = KTree.node A10K2.u2507 (nat_lit 42673609) (nat_lit 4761499622) (nat_lit 0) A10K2.u2508 from rfl, totK_node, atot2507, atot2508]
  decide +kernel

theorem arows2512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2512 = true := by
  rw [show A10K2.u2512 = KTree.node A10K2.u2510 (nat_lit 42692242) (nat_lit 15544065974) (nat_lit 0) A10K2.u2511 from rfl, allE_node, arows2510, irow2512, arows2511]
  all_goals rfl

theorem atot2512 : totK PA10K2 A10K2.u2512 = [798450316783, 4330406076258, 8124174784906, 5787590282983, 1316639173173, 69028654569, 0, 0, 0, 0] := by
  rw [show A10K2.u2512 = KTree.node A10K2.u2510 (nat_lit 42692242) (nat_lit 15544065974) (nat_lit 0) A10K2.u2511 from rfl, totK_node, atot2510, atot2511]
  decide +kernel

theorem arows2516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2516 = true := by
  rw [show A10K2.u2516 = KTree.node A10K2.u2514 (nat_lit 42711222) (nat_lit 15231869848) (nat_lit 0) A10K2.u2515 from rfl, allE_node, arows2514, irow2516, arows2515]
  all_goals rfl

theorem atot2516 : totK PA10K2 A10K2.u2516 = [0, 1396352331029, 6173385244993, 8510311899371, 3773094065659, 412844781846, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u2516 = KTree.node A10K2.u2514 (nat_lit 42711222) (nat_lit 15231869848) (nat_lit 0) A10K2.u2515 from rfl, totK_node, atot2514, atot2515]
  decide +kernel

theorem arows2519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2519 = true := by
  rw [show A10K2.u2519 = KTree.node A10K2.u2517 (nat_lit 42804973) (nat_lit 5399166982) (nat_lit 0) A10K2.u2518 from rfl, allE_node, arows2517, irow2519, arows2518]
  all_goals rfl

theorem atot2519 : totK PA10K2 A10K2.u2519 = [0, 857710904603, 4378389721608, 7658191372226, 5426413418618, 1361571333908, 86844659398, 0, 0, 0] := by
  rw [show A10K2.u2519 = KTree.node A10K2.u2517 (nat_lit 42804973) (nat_lit 5399166982) (nat_lit 0) A10K2.u2518 from rfl, totK_node, atot2517, atot2518]
  decide +kernel

theorem arows2525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2525 = true := by
  rw [show A10K2.u2525 = KTree.node A10K2.u2523 (nat_lit 42814008) (nat_lit 7882156372) (nat_lit 0) A10K2.u2524 from rfl, allE_node, arows2523, irow2525, arows2524]
  all_goals rfl

theorem atot2525 : totK PA10K2 A10K2.u2525 = [0, 1211784469564, 5455500326673, 8041274362180, 3957582865751, 503604348427, 12273889295, 0, 0, 0] := by
  rw [show A10K2.u2525 = KTree.node A10K2.u2523 (nat_lit 42814008) (nat_lit 7882156372) (nat_lit 0) A10K2.u2524 from rfl, totK_node, atot2523, atot2524]
  decide +kernel

theorem arows2528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2528 = true := by
  rw [show A10K2.u2528 = KTree.node A10K2.u2526 (nat_lit 42837228) (nat_lit 11593005882) (nat_lit 0) A10K2.u2527 from rfl, allE_node, arows2526, irow2528, arows2527]
  all_goals rfl

theorem atot2528 : totK PA10K2 A10K2.u2528 = [0, 224689426326, 2481651782345, 7166173322102, 7349740397556, 2423819429366, 242407306182, 9729745405, 0, 0] := by
  rw [show A10K2.u2528 = KTree.node A10K2.u2526 (nat_lit 42837228) (nat_lit 11593005882) (nat_lit 0) A10K2.u2527 from rfl, totK_node, atot2526, atot2527]
  decide +kernel

theorem arows2532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2532 = true := by
  rw [show A10K2.u2532 = KTree.node A10K2.u2530 (nat_lit 42846422) (nat_lit 12138754253) (nat_lit 0) A10K2.u2531 from rfl, allE_node, arows2530, irow2532, arows2531]
  all_goals rfl

theorem atot2532 : totK PA10K2 A10K2.u2532 = [0, 0, 1147718140910, 5277105769654, 7782353055473, 3829126398188, 638402905493, 21532950751, 0, 0] := by
  rw [show A10K2.u2532 = KTree.node A10K2.u2530 (nat_lit 42846422) (nat_lit 12138754253) (nat_lit 0) A10K2.u2531 from rfl, totK_node, atot2530, atot2531]
  decide +kernel

theorem arows2535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2535 = true := by
  rw [show A10K2.u2535 = KTree.node A10K2.u2533 (nat_lit 42866800) (nat_lit 14126752022) (nat_lit 0) A10K2.u2534 from rfl, allE_node, arows2533, irow2535, arows2534]
  all_goals rfl

theorem atot2535 : totK PA10K2 A10K2.u2535 = [0, 1306223671615, 5605297211999, 7810976656778, 3879943691457, 686014531605, 36736648791, 0, 0, 0] := by
  rw [show A10K2.u2535 = KTree.node A10K2.u2533 (nat_lit 42866800) (nat_lit 14126752022) (nat_lit 0) A10K2.u2534 from rfl, totK_node, atot2533, atot2534]
  decide +kernel

theorem arows2540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2540 = true := by
  rw [show A10K2.u2540 = KTree.node A10K2.u2538 (nat_lit 42878244) (nat_lit 13973624068) (nat_lit 0) A10K2.u2539 from rfl, allE_node, arows2538, irow2540, arows2539]
  all_goals rfl

theorem atot2540 : totK PA10K2 A10K2.u2540 = [0, 810058863673, 4468152176511, 7987758544055, 4770326381759, 783883037737, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2540 = KTree.node A10K2.u2538 (nat_lit 42878244) (nat_lit 13973624068) (nat_lit 0) A10K2.u2539 from rfl, totK_node, atot2538, atot2539]
  decide +kernel

theorem arows2543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2543 = true := by
  rw [show A10K2.u2543 = KTree.node A10K2.u2541 (nat_lit 42904069) (nat_lit 6791634080) (nat_lit 0) A10K2.u2542 from rfl, allE_node, arows2541, irow2543, arows2542]
  all_goals rfl

theorem atot2543 : totK PA10K2 A10K2.u2543 = [0, 0, 2104165421512, 7528253779736, 7423981292054, 1716877002057, 88046306286, 0, 0, 0] := by
  rw [show A10K2.u2543 = KTree.node A10K2.u2541 (nat_lit 42904069) (nat_lit 6791634080) (nat_lit 0) A10K2.u2542 from rfl, totK_node, atot2541, atot2542]
  decide +kernel

theorem arows2547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2547 = true := by
  rw [show A10K2.u2547 = KTree.node A10K2.u2545 (nat_lit 42936978) (nat_lit 15529038244) (nat_lit 0) A10K2.u2546 from rfl, allE_node, arows2545, irow2547, arows2546]
  all_goals rfl

theorem atot2547 : totK PA10K2 A10K2.u2547 = [0, 808145238817, 3767494763414, 6682657959294, 5815133129136, 2058650577320, 245934626035, 6239673734, 0, 0] := by
  rw [show A10K2.u2547 = KTree.node A10K2.u2545 (nat_lit 42936978) (nat_lit 15529038244) (nat_lit 0) A10K2.u2546 from rfl, totK_node, atot2545, atot2546]
  decide +kernel

theorem arows2550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2550 = true := by
  rw [show A10K2.u2550 = KTree.node A10K2.u2548 (nat_lit 42955670) (nat_lit 15693259330) (nat_lit 0) A10K2.u2549 from rfl, allE_node, arows2548, irow2550, arows2549]
  all_goals rfl

theorem atot2550 : totK PA10K2 A10K2.u2550 = [444521281299, 2234527935506, 5119772279806, 6762851206777, 4521596530240, 1089357916812, 62382159641, 0, 0, 0] := by
  rw [show A10K2.u2550 = KTree.node A10K2.u2548 (nat_lit 42955670) (nat_lit 15693259330) (nat_lit 0) A10K2.u2549 from rfl, totK_node, atot2548, atot2549]
  decide +kernel

theorem arows2560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2560 = true := by
  rw [show A10K2.u2560 = KTree.node A10K2.u2558 (nat_lit 42999172) (nat_lit 7922537177) (nat_lit 0) A10K2.u2559 from rfl, allE_node, arows2558, irow2560, arows2559]
  all_goals rfl

theorem atot2560 : totK PA10K2 A10K2.u2560 = [1085175609241, 5245892488514, 7936134316357, 4166682215349, 680132895968, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2560 = KTree.node A10K2.u2558 (nat_lit 42999172) (nat_lit 7922537177) (nat_lit 0) A10K2.u2559 from rfl, totK_node, atot2558, atot2559]
  decide +kernel

theorem arows2563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2563 = true := by
  rw [show A10K2.u2563 = KTree.node A10K2.u2561 (nat_lit 43024741) (nat_lit 7183738090) (nat_lit 0) A10K2.u2562 from rfl, allE_node, arows2561, irow2563, arows2562]
  all_goals rfl

theorem atot2563 : totK PA10K2 A10K2.u2563 = [266424507814, 2454007396026, 6710399462960, 6732019229494, 2507206034775, 403634277302, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2563 = KTree.node A10K2.u2561 (nat_lit 43024741) (nat_lit 7183738090) (nat_lit 0) A10K2.u2562 from rfl, totK_node, atot2561, atot2562]
  decide +kernel

theorem arows2567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2567 = true := by
  rw [show A10K2.u2567 = KTree.node A10K2.u2565 (nat_lit 43043500) (nat_lit 13092961586) (nat_lit 0) A10K2.u2566 from rfl, allE_node, arows2565, irow2567, arows2566]
  all_goals rfl

theorem atot2567 : totK PA10K2 A10K2.u2567 = [311769148082, 1950602796084, 5535016393410, 7308692241302, 3372943931804, 441386055257, 10957026886, 0, 0, 0] := by
  rw [show A10K2.u2567 = KTree.node A10K2.u2565 (nat_lit 43043500) (nat_lit 13092961586) (nat_lit 0) A10K2.u2566 from rfl, totK_node, atot2565, atot2566]
  decide +kernel

theorem arows2570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2570 = true := by
  rw [show A10K2.u2570 = KTree.node A10K2.u2568 (nat_lit 43071658) (nat_lit 12841543123) (nat_lit 0) A10K2.u2569 from rfl, allE_node, arows2568, irow2570, arows2569]
  all_goals rfl

theorem atot2570 : totK PA10K2 A10K2.u2570 = [1285766466569, 5424257643903, 7693725714720, 4152760454780, 700495707538, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u2570 = KTree.node A10K2.u2568 (nat_lit 43071658) (nat_lit 12841543123) (nat_lit 0) A10K2.u2569 from rfl, totK_node, atot2568, atot2569]
  decide +kernel

theorem arows2575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2575 = true := by
  rw [show A10K2.u2575 = KTree.node A10K2.u2573 (nat_lit 43085198) (nat_lit 15185175319) (nat_lit 0) A10K2.u2574 from rfl, allE_node, arows2573, irow2575, arows2574]
  all_goals rfl

theorem atot2575 : totK PA10K2 A10K2.u2575 = [502723522018, 3798518419412, 8207183476656, 5848804240460, 1347751389429, 82435262785, 0, 0, 0, 0] := by
  rw [show A10K2.u2575 = KTree.node A10K2.u2573 (nat_lit 43085198) (nat_lit 15185175319) (nat_lit 0) A10K2.u2574 from rfl, totK_node, atot2573, atot2574]
  decide +kernel

theorem arows2578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2578 = true := by
  rw [show A10K2.u2578 = KTree.node A10K2.u2576 (nat_lit 43105059) (nat_lit 9871997345) (nat_lit 0) A10K2.u2577 from rfl, allE_node, arows2576, irow2578, arows2577]
  all_goals rfl

theorem atot2578 : totK PA10K2 A10K2.u2578 = [0, 1223630881002, 5527744127365, 7909496022121, 3809355787238, 621463767656, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u2578 = KTree.node A10K2.u2576 (nat_lit 43105059) (nat_lit 9871997345) (nat_lit 0) A10K2.u2577 from rfl, totK_node, atot2576, atot2577]
  decide +kernel

theorem arows2582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2582 = true := by
  rw [show A10K2.u2582 = KTree.node A10K2.u2580 (nat_lit 43122796) (nat_lit 11430996088) (nat_lit 0) A10K2.u2581 from rfl, allE_node, arows2580, irow2582, arows2581]
  all_goals rfl

theorem atot2582 : totK PA10K2 A10K2.u2582 = [696624018698, 3418548774394, 6298594680602, 5806885468279, 2469556546052, 302716611113, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2582 = KTree.node A10K2.u2580 (nat_lit 43122796) (nat_lit 11430996088) (nat_lit 0) A10K2.u2581 from rfl, totK_node, atot2580, atot2581]
  decide +kernel

theorem arows2585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2585 = true := by
  rw [show A10K2.u2585 = KTree.node A10K2.u2583 (nat_lit 43134674) (nat_lit 15347524877) (nat_lit 0) A10K2.u2584 from rfl, allE_node, arows2583, irow2585, arows2584]
  all_goals rfl

theorem atot2585 : totK PA10K2 A10K2.u2585 = [1031819552733, 4762456701556, 7745477389648, 4681636794894, 845374708173, 37229241746, 0, 0, 0, 0] := by
  rw [show A10K2.u2585 = KTree.node A10K2.u2583 (nat_lit 43134674) (nat_lit 15347524877) (nat_lit 0) A10K2.u2584 from rfl, totK_node, atot2583, atot2584]
  decide +kernel

theorem arows2591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2591 = true := by
  rw [show A10K2.u2591 = KTree.node A10K2.u2589 (nat_lit 43145494) (nat_lit 8471380067) (nat_lit 0) A10K2.u2590 from rfl, allE_node, arows2589, irow2591, arows2590]
  all_goals rfl

theorem atot2591 : totK PA10K2 A10K2.u2591 = [568096137437, 3948298298299, 7929765434922, 5342979170150, 1057064721719, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u2591 = KTree.node A10K2.u2589 (nat_lit 43145494) (nat_lit 8471380067) (nat_lit 0) A10K2.u2590 from rfl, totK_node, atot2589, atot2590]
  decide +kernel

theorem arows2594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2594 = true := by
  rw [show A10K2.u2594 = KTree.node A10K2.u2592 (nat_lit 43173276) (nat_lit 9208462248) (nat_lit 0) A10K2.u2593 from rfl, allE_node, arows2592, irow2594, arows2593]
  all_goals rfl

theorem atot2594 : totK PA10K2 A10K2.u2594 = [0, 1398350981862, 6049252043531, 8017528255927, 3056065327220, 355384936875, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2594 = KTree.node A10K2.u2592 (nat_lit 43173276) (nat_lit 9208462248) (nat_lit 0) A10K2.u2593 from rfl, totK_node, atot2592, atot2593]
  decide +kernel

theorem arows2598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2598 = true := by
  rw [show A10K2.u2598 = KTree.node A10K2.u2596 (nat_lit 43258644) (nat_lit 12079295292) (nat_lit 0) A10K2.u2597 from rfl, allE_node, arows2596, irow2598, arows2597]
  all_goals rfl

theorem atot2598 : totK PA10K2 A10K2.u2598 = [0, 1326866312469, 5538868206005, 7618262097867, 3857588556807, 651360991465, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u2598 = KTree.node A10K2.u2596 (nat_lit 43258644) (nat_lit 12079295292) (nat_lit 0) A10K2.u2597 from rfl, totK_node, atot2596, atot2597]
  decide +kernel

theorem arows2601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2601 = true := by
  rw [show A10K2.u2601 = KTree.node A10K2.u2599 (nat_lit 43279295) (nat_lit 14174167974) (nat_lit 0) A10K2.u2600 from rfl, allE_node, arows2599, irow2601, arows2600]
  all_goals rfl

theorem atot2601 : totK PA10K2 A10K2.u2601 = [0, 1191723596537, 5564196253612, 8052618053231, 3866288801143, 545892798599, 13207830636, 0, 0, 0] := by
  rw [show A10K2.u2601 = KTree.node A10K2.u2599 (nat_lit 43279295) (nat_lit 14174167974) (nat_lit 0) A10K2.u2600 from rfl, totK_node, atot2599, atot2600]
  decide +kernel

theorem arows2606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2606 = true := by
  rw [show A10K2.u2606 = KTree.node A10K2.u2604 (nat_lit 43336876) (nat_lit 12833588919) (nat_lit 0) A10K2.u2605 from rfl, allE_node, arows2604, irow2606, arows2605]
  all_goals rfl

theorem atot2606 : totK PA10K2 A10K2.u2606 = [0, 779803666384, 4514470593353, 8130324792379, 4799701820279, 769917513614, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u2606 = KTree.node A10K2.u2604 (nat_lit 43336876) (nat_lit 12833588919) (nat_lit 0) A10K2.u2605 from rfl, totK_node, atot2604, atot2605]
  decide +kernel

theorem arows2609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2609 = true := by
  rw [show A10K2.u2609 = KTree.node A10K2.u2607 (nat_lit 43384882) (nat_lit 6378283606) (nat_lit 0) A10K2.u2608 from rfl, allE_node, arows2607, irow2609, arows2608]
  all_goals rfl

theorem atot2609 : totK PA10K2 A10K2.u2609 = [0, 1198350617909, 5215088530103, 7708753702593, 4352058347897, 798506747105, 37931615632, 0, 0, 0] := by
  rw [show A10K2.u2609 = KTree.node A10K2.u2607 (nat_lit 43384882) (nat_lit 6378283606) (nat_lit 0) A10K2.u2608 from rfl, totK_node, atot2607, atot2608]
  decide +kernel

theorem arows2613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2613 = true := by
  rw [show A10K2.u2613 = KTree.node A10K2.u2611 (nat_lit 43396786) (nat_lit 15032768103) (nat_lit 0) A10K2.u2612 from rfl, allE_node, arows2611, irow2613, arows2612]
  all_goals rfl

theorem atot2613 : totK PA10K2 A10K2.u2613 = [0, 1091240905297, 4889683373247, 7763124163154, 4391492991790, 723692947542, 36463937579, 0, 0, 0] := by
  rw [show A10K2.u2613 = KTree.node A10K2.u2611 (nat_lit 43396786) (nat_lit 15032768103) (nat_lit 0) A10K2.u2612 from rfl, totK_node, atot2611, atot2612]
  decide +kernel

theorem arows2616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2616 = true := by
  rw [show A10K2.u2616 = KTree.node A10K2.u2614 (nat_lit 43407680) (nat_lit 13590559885) (nat_lit 0) A10K2.u2615 from rfl, allE_node, arows2614, irow2616, arows2615]
  all_goals rfl

theorem atot2616 : totK PA10K2 A10K2.u2616 = [0, 504455776963, 3822486255374, 7921935149205, 5286973172686, 1010774086172, 57372072225, 0, 0, 0] := by
  rw [show A10K2.u2616 = KTree.node A10K2.u2614 (nat_lit 43407680) (nat_lit 13590559885) (nat_lit 0) A10K2.u2615 from rfl, totK_node, atot2614, atot2615]
  decide +kernel

theorem arows2623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2623 = true := by
  rw [show A10K2.u2623 = KTree.node A10K2.u2621 (nat_lit 43436130) (nat_lit 9115693092) (nat_lit 0) A10K2.u2622 from rfl, allE_node, arows2621, irow2623, arows2622]
  all_goals rfl

theorem atot2623 : totK PA10K2 A10K2.u2623 = [0, 317769054122, 2242165059991, 6210254219607, 6880438576271, 2583154551805, 327590491638, 6354482628, 0, 0] := by
  rw [show A10K2.u2623 = KTree.node A10K2.u2621 (nat_lit 43436130) (nat_lit 9115693092) (nat_lit 0) A10K2.u2622 from rfl, totK_node, atot2621, atot2622]
  decide +kernel

theorem arows2626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2626 = true := by
  rw [show A10K2.u2626 = KTree.node A10K2.u2624 (nat_lit 44046500) (nat_lit 13467021486) (nat_lit 0) A10K2.u2625 from rfl, allE_node, arows2624, irow2626, arows2625]
  all_goals rfl

theorem atot2626 : totK PA10K2 A10K2.u2626 = [0, 1267285094957, 5463129601224, 7734971543345, 3954801888386, 651412845592, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2626 = KTree.node A10K2.u2624 (nat_lit 44046500) (nat_lit 13467021486) (nat_lit 0) A10K2.u2625 from rfl, totK_node, atot2624, atot2625]
  decide +kernel

theorem arows2630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2630 = true := by
  rw [show A10K2.u2630 = KTree.node A10K2.u2628 (nat_lit 44068242) (nat_lit 13587771334) (nat_lit 0) A10K2.u2629 from rfl, allE_node, arows2628, irow2630, arows2629]
  all_goals rfl

theorem atot2630 : totK PA10K2 A10K2.u2630 = [0, 593403324104, 3995547459306, 8208251800165, 5719276158001, 1139121589003, 47212543301, 0, 0, 0] := by
  rw [show A10K2.u2630 = KTree.node A10K2.u2628 (nat_lit 44068242) (nat_lit 13587771334) (nat_lit 0) A10K2.u2629 from rfl, totK_node, atot2628, atot2629]
  decide +kernel

theorem arows2633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2633 = true := by
  rw [show A10K2.u2633 = KTree.node A10K2.u2631 (nat_lit 44079269) (nat_lit 7225095799) (nat_lit 0) A10K2.u2632 from rfl, allE_node, arows2631, irow2633, arows2632]
  all_goals rfl

theorem atot2633 : totK PA10K2 A10K2.u2633 = [0, 0, 1262987945387, 5566474576720, 7730839988075, 3632014785805, 612138080085, 30650496230, 0, 0] := by
  rw [show A10K2.u2633 = KTree.node A10K2.u2631 (nat_lit 44079269) (nat_lit 7225095799) (nat_lit 0) A10K2.u2632 from rfl, totK_node, atot2631, atot2632]
  decide +kernel

theorem arows2638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2638 = true := by
  rw [show A10K2.u2638 = KTree.node A10K2.u2636 (nat_lit 44101270) (nat_lit 15381232080) (nat_lit 0) A10K2.u2637 from rfl, allE_node, arows2636, irow2638, arows2637]
  all_goals rfl

theorem atot2638 : totK PA10K2 A10K2.u2638 = [0, 767063984985, 3684655545767, 6682106104578, 5846706093588, 2214033125913, 248877833895, 5546304973, 0, 0] := by
  rw [show A10K2.u2638 = KTree.node A10K2.u2636 (nat_lit 44101270) (nat_lit 15381232080) (nat_lit 0) A10K2.u2637 from rfl, totK_node, atot2636, atot2637]
  decide +kernel

theorem arows2641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2641 = true := by
  rw [show A10K2.u2641 = KTree.node A10K2.u2639 (nat_lit 44182273) (nat_lit 9776660226) (nat_lit 0) A10K2.u2640 from rfl, allE_node, arows2639, irow2641, arows2640]
  all_goals rfl

theorem atot2641 : totK PA10K2 A10K2.u2641 = [0, 1071132957616, 4674319884884, 7379111059192, 4814256181512, 1036243081730, 62165360546, 0, 0, 0] := by
  rw [show A10K2.u2641 = KTree.node A10K2.u2639 (nat_lit 44182273) (nat_lit 9776660226) (nat_lit 0) A10K2.u2640 from rfl, totK_node, atot2639, atot2640]
  decide +kernel

theorem arows2645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2645 = true := by
  rw [show A10K2.u2645 = KTree.node A10K2.u2643 (nat_lit 44204074) (nat_lit 7139365157) (nat_lit 0) A10K2.u2644 from rfl, allE_node, arows2643, irow2645, arows2644]
  all_goals rfl

theorem atot2645 : totK PA10K2 A10K2.u2645 = [0, 304053839609, 3192451893206, 7884065717491, 6201965839536, 1368839648041, 70818940565, 0, 0, 0] := by
  rw [show A10K2.u2645 = KTree.node A10K2.u2643 (nat_lit 44204074) (nat_lit 7139365157) (nat_lit 0) A10K2.u2644 from rfl, totK_node, atot2643, atot2644]
  decide +kernel

theorem arows2648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2648 = true := by
  rw [show A10K2.u2648 = KTree.node A10K2.u2646 (nat_lit 44223024) (nat_lit 13416512417) (nat_lit 0) A10K2.u2647 from rfl, allE_node, arows2646, irow2648, arows2647]
  all_goals rfl

theorem atot2648 : totK PA10K2 A10K2.u2648 = [0, 482054232543, 2547967532830, 6162325142061, 6716030976652, 2510241579181, 322395268869, 6354482628, 0, 0] := by
  rw [show A10K2.u2648 = KTree.node A10K2.u2646 (nat_lit 44223024) (nat_lit 13416512417) (nat_lit 0) A10K2.u2647 from rfl, totK_node, atot2646, atot2647]
  decide +kernel

theorem arows2654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2654 = true := by
  rw [show A10K2.u2654 = KTree.node A10K2.u2652 (nat_lit 44645125) (nat_lit 6907801568) (nat_lit 0) A10K2.u2653 from rfl, allE_node, arows2652, irow2654, arows2653]
  all_goals rfl

theorem atot2654 : totK PA10K2 A10K2.u2654 = [0, 1121088796758, 5307047317560, 7888287091898, 4181608136811, 701440652494, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2654 = KTree.node A10K2.u2652 (nat_lit 44645125) (nat_lit 6907801568) (nat_lit 0) A10K2.u2653 from rfl, totK_node, atot2652, atot2653]
  decide +kernel

theorem arows2657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2657 = true := by
  rw [show A10K2.u2657 = KTree.node A10K2.u2655 (nat_lit 44658118) (nat_lit 15871218281) (nat_lit 0) A10K2.u2656 from rfl, allE_node, arows2655, irow2657, arows2656]
  all_goals rfl

theorem atot2657 : totK PA10K2 A10K2.u2657 = [0, 695123071544, 4246507579310, 8314713657474, 5657820717883, 1146969573623, 48434374484, 0, 0, 0] := by
  rw [show A10K2.u2657 = KTree.node A10K2.u2655 (nat_lit 44658118) (nat_lit 15871218281) (nat_lit 0) A10K2.u2656 from rfl, totK_node, atot2655, atot2656]
  decide +kernel

theorem arows2661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2661 = true := by
  rw [show A10K2.u2661 = KTree.node A10K2.u2659 (nat_lit 44677050) (nat_lit 13748579757) (nat_lit 0) A10K2.u2660 from rfl, allE_node, arows2659, irow2661, arows2660]
  all_goals rfl

theorem atot2661 : totK PA10K2 A10K2.u2661 = [0, 0, 1280573093275, 5568641338199, 7777065228181, 3759026513307, 630851240957, 31082886609, 0, 0] := by
  rw [show A10K2.u2661 = KTree.node A10K2.u2659 (nat_lit 44677050) (nat_lit 13748579757) (nat_lit 0) A10K2.u2660 from rfl, totK_node, atot2659, atot2660]
  decide +kernel

theorem arows2664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2664 = true := by
  rw [show A10K2.u2664 = KTree.node A10K2.u2662 (nat_lit 44690504) (nat_lit 10359444654) (nat_lit 0) A10K2.u2663 from rfl, allE_node, arows2662, irow2664, arows2663]
  all_goals rfl

theorem atot2664 : totK PA10K2 A10K2.u2664 = [0, 516552094339, 2801135280160, 6208104433878, 6666654569543, 2661160456165, 282448502296, 6121173289, 0, 0] := by
  rw [show A10K2.u2664 = KTree.node A10K2.u2662 (nat_lit 44690504) (nat_lit 10359444654) (nat_lit 0) A10K2.u2663 from rfl, totK_node, atot2662, atot2663]
  decide +kernel

theorem arows2669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2669 = true := by
  rw [show A10K2.u2669 = KTree.node A10K2.u2667 (nat_lit 44707476) (nat_lit 10746150214) (nat_lit 0) A10K2.u2668 from rfl, allE_node, arows2667, irow2669, arows2668]
  all_goals rfl

theorem atot2669 : totK PA10K2 A10K2.u2669 = [0, 1016520499691, 4742529494119, 7659697906405, 4815154988179, 931290971814, 42529659924, 0, 0, 0] := by
  rw [show A10K2.u2669 = KTree.node A10K2.u2667 (nat_lit 44707476) (nat_lit 10746150214) (nat_lit 0) A10K2.u2668 from rfl, totK_node, atot2667, atot2668]
  decide +kernel

theorem arows2672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2672 = true := by
  rw [show A10K2.u2672 = KTree.node A10K2.u2670 (nat_lit 44718317) (nat_lit 5975387072) (nat_lit 0) A10K2.u2671 from rfl, allE_node, arows2670, irow2672, arows2671]
  all_goals rfl

theorem atot2672 : totK PA10K2 A10K2.u2672 = [0, 583209941258, 3792331393115, 7724399373551, 5534299105690, 1176691738253, 64029076578, 0, 0, 0] := by
  rw [show A10K2.u2672 = KTree.node A10K2.u2670 (nat_lit 44718317) (nat_lit 5975387072) (nat_lit 0) A10K2.u2671 from rfl, totK_node, atot2670, atot2671]
  decide +kernel

theorem arows2676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2676 = true := by
  rw [show A10K2.u2676 = KTree.node A10K2.u2674 (nat_lit 44746784) (nat_lit 13722426567) (nat_lit 0) A10K2.u2675 from rfl, allE_node, arows2674, irow2676, arows2675]
  all_goals rfl

theorem atot2676 : totK PA10K2 A10K2.u2676 = [0, 311517321411, 2223347521406, 6172942438460, 7159504939624, 2686525835348, 329268602014, 6354482628, 0, 0] := by
  rw [show A10K2.u2676 = KTree.node A10K2.u2674 (nat_lit 44746784) (nat_lit 13722426567) (nat_lit 0) A10K2.u2675 from rfl, totK_node, atot2674, atot2675]
  decide +kernel

theorem arows2679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2679 = true := by
  rw [show A10K2.u2679 = KTree.node A10K2.u2677 (nat_lit 44775749) (nat_lit 6757064207) (nat_lit 0) A10K2.u2678 from rfl, allE_node, arows2677, irow2679, arows2678]
  all_goals rfl

theorem atot2679 : totK PA10K2 A10K2.u2679 = [0, 1298181293276, 5691844571109, 8255259500326, 4278060364014, 697075500687, 31522233512, 0, 0, 0] := by
  rw [show A10K2.u2679 = KTree.node A10K2.u2677 (nat_lit 44775749) (nat_lit 6757064207) (nat_lit 0) A10K2.u2678 from rfl, totK_node, atot2677, atot2678]
  decide +kernel

theorem arows2687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2687 = true := by
  rw [show A10K2.u2687 = KTree.node A10K2.u2685 (nat_lit 44803731) (nat_lit 10993800162) (nat_lit 0) A10K2.u2686 from rfl, allE_node, arows2685, irow2687, arows2686]
  all_goals rfl

theorem atot2687 : totK PA10K2 A10K2.u2687 = [0, 0, 1688787491865, 6735931772178, 8203318916661, 3186473123035, 351543214848, 7047025452, 0, 0] := by
  rw [show A10K2.u2687 = KTree.node A10K2.u2685 (nat_lit 44803731) (nat_lit 10993800162) (nat_lit 0) A10K2.u2686 from rfl, totK_node, atot2685, atot2686]
  decide +kernel

theorem arows2690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2690 = true := by
  rw [show A10K2.u2690 = KTree.node A10K2.u2688 (nat_lit 45089088) (nat_lit 14925203453) (nat_lit 0) A10K2.u2689 from rfl, allE_node, arows2688, irow2690, arows2689]
  all_goals rfl

theorem atot2690 : totK PA10K2 A10K2.u2690 = [0, 761005751305, 3911807975745, 7235983494827, 5882753302693, 1823219969222, 131725500527, 0, 0, 0] := by
  rw [show A10K2.u2690 = KTree.node A10K2.u2688 (nat_lit 45089088) (nat_lit 14925203453) (nat_lit 0) A10K2.u2689 from rfl, totK_node, atot2688, atot2689]
  decide +kernel

theorem arows2694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2694 = true := by
  rw [show A10K2.u2694 = KTree.node A10K2.u2692 (nat_lit 45107539) (nat_lit 10126734527) (nat_lit 0) A10K2.u2693 from rfl, allE_node, arows2692, irow2694, arows2693]
  all_goals rfl

theorem atot2694 : totK PA10K2 A10K2.u2694 = [0, 1045008235948, 5128859000430, 8090424799228, 4217960135210, 580255868159, 11814975521, 0, 0, 0] := by
  rw [show A10K2.u2694 = KTree.node A10K2.u2692 (nat_lit 45107539) (nat_lit 10126734527) (nat_lit 0) A10K2.u2693 from rfl, totK_node, atot2692, atot2693]
  decide +kernel

theorem arows2697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2697 = true := by
  rw [show A10K2.u2697 = KTree.node A10K2.u2695 (nat_lit 45125914) (nat_lit 6411282269) (nat_lit 0) A10K2.u2696 from rfl, allE_node, arows2695, irow2697, arows2696]
  all_goals rfl

theorem atot2697 : totK PA10K2 A10K2.u2697 = [0, 0, 1364565144824, 5886600068882, 7785849430180, 3297018893132, 512117714932, 30220878370, 0, 0] := by
  rw [show A10K2.u2697 = KTree.node A10K2.u2695 (nat_lit 45125914) (nat_lit 6411282269) (nat_lit 0) A10K2.u2696 from rfl, totK_node, atot2695, atot2696]
  decide +kernel

theorem arows2702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2702 = true := by
  rw [show A10K2.u2702 = KTree.node A10K2.u2700 (nat_lit 45147059) (nat_lit 5852116129) (nat_lit 0) A10K2.u2701 from rfl, allE_node, arows2700, irow2702, arows2701]
  all_goals rfl

theorem atot2702 : totK PA10K2 A10K2.u2702 = [0, 814371176014, 3838636354122, 6809272009977, 5577919989824, 1866564892308, 213555341488, 5546304973, 0, 0] := by
  rw [show A10K2.u2702 = KTree.node A10K2.u2700 (nat_lit 45147059) (nat_lit 5852116129) (nat_lit 0) A10K2.u2701 from rfl, totK_node, atot2700, atot2701]
  decide +kernel

theorem arows2705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2705 = true := by
  rw [show A10K2.u2705 = KTree.node A10K2.u2703 (nat_lit 45172545) (nat_lit 5595386156) (nat_lit 0) A10K2.u2704 from rfl, allE_node, arows2703, irow2705, arows2704]
  all_goals rfl

theorem atot2705 : totK PA10K2 A10K2.u2705 = [0, 1065016858459, 4850228330204, 7690805831015, 4638084029696, 867133956449, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u2705 = KTree.node A10K2.u2703 (nat_lit 45172545) (nat_lit 5595386156) (nat_lit 0) A10K2.u2704 from rfl, totK_node, atot2703, atot2704]
  decide +kernel

theorem arows2709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2709 = true := by
  rw [show A10K2.u2709 = KTree.node A10K2.u2707 (nat_lit 45196986) (nat_lit 14950583633) (nat_lit 0) A10K2.u2708 from rfl, allE_node, arows2707, irow2709, arows2708]
  all_goals rfl

theorem atot2709 : totK PA10K2 A10K2.u2709 = [0, 218175288971, 2417365384740, 6960670815058, 7142379774715, 2510516770374, 355490816378, 25130442608, 0, 0] := by
  rw [show A10K2.u2709 = KTree.node A10K2.u2707 (nat_lit 45196986) (nat_lit 14950583633) (nat_lit 0) A10K2.u2708 from rfl, totK_node, atot2707, atot2708]
  decide +kernel

theorem arows2712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2712 = true := by
  rw [show A10K2.u2712 = KTree.node A10K2.u2710 (nat_lit 45207817) (nat_lit 8850314757) (nat_lit 0) A10K2.u2711 from rfl, allE_node, arows2710, irow2712, arows2711]
  all_goals rfl

theorem atot2712 : totK PA10K2 A10K2.u2712 = [0, 162078939081, 1641695921778, 5852107954111, 7778386531641, 3331072961906, 420062141041, 11638555097, 0, 0] := by
  rw [show A10K2.u2712 = KTree.node A10K2.u2710 (nat_lit 45207817) (nat_lit 8850314757) (nat_lit 0) A10K2.u2711 from rfl, totK_node, atot2710, atot2711]
  decide +kernel

theorem arows2718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2718 = true := by
  rw [show A10K2.u2718 = KTree.node A10K2.u2716 (nat_lit 45226096) (nat_lit 14427180537) (nat_lit 0) A10K2.u2717 from rfl, allE_node, arows2716, irow2718, arows2717]
  all_goals rfl

theorem atot2718 : totK PA10K2 A10K2.u2718 = [0, 1280465187049, 5552007589412, 7635324350182, 3663746813632, 573366554040, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u2718 = KTree.node A10K2.u2716 (nat_lit 45226096) (nat_lit 14427180537) (nat_lit 0) A10K2.u2717 from rfl, totK_node, atot2716, atot2717]
  decide +kernel

theorem arows2721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2721 = true := by
  rw [show A10K2.u2721 = KTree.node A10K2.u2719 (nat_lit 45237439) (nat_lit 10585229601) (nat_lit 0) A10K2.u2720 from rfl, allE_node, arows2719, irow2721, arows2720]
  all_goals rfl

theorem atot2721 : totK PA10K2 A10K2.u2721 = [0, 848550019351, 4700876854491, 8103679747718, 4579436851226, 701999749119, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u2721 = KTree.node A10K2.u2719 (nat_lit 45237439) (nat_lit 10585229601) (nat_lit 0) A10K2.u2720 from rfl, totK_node, atot2719, atot2720]
  decide +kernel

theorem arows2725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2725 = true := by
  rw [show A10K2.u2725 = KTree.node A10K2.u2723 (nat_lit 45262494) (nat_lit 14233278094) (nat_lit 0) A10K2.u2724 from rfl, allE_node, arows2723, irow2725, arows2724]
  all_goals rfl

theorem atot2725 : totK PA10K2 A10K2.u2725 = [0, 0, 1972558959827, 7282466289790, 7557474847428, 1867718971707, 108347318831, 0, 0, 0] := by
  rw [show A10K2.u2725 = KTree.node A10K2.u2723 (nat_lit 45262494) (nat_lit 14233278094) (nat_lit 0) A10K2.u2724 from rfl, totK_node, atot2723, atot2724]
  decide +kernel

theorem arows2728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2728 = true := by
  rw [show A10K2.u2728 = KTree.node A10K2.u2726 (nat_lit 45351181) (nat_lit 5875885541) (nat_lit 0) A10K2.u2727 from rfl, allE_node, arows2726, irow2728, arows2727]
  all_goals rfl

theorem atot2728 : totK PA10K2 A10K2.u2728 = [0, 0, 1067258280551, 5262534670013, 8001940592024, 3798240693781, 607797095364, 31296045761, 0, 0] := by
  rw [show A10K2.u2728 = KTree.node A10K2.u2726 (nat_lit 45351181) (nat_lit 5875885541) (nat_lit 0) A10K2.u2727 from rfl, totK_node, atot2726, atot2727]
  decide +kernel

theorem arows2733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2733 = true := by
  rw [show A10K2.u2733 = KTree.node A10K2.u2731 (nat_lit 45369905) (nat_lit 9666776453) (nat_lit 0) A10K2.u2732 from rfl, allE_node, arows2731, irow2733, arows2732]
  all_goals rfl

theorem atot2733 : totK PA10K2 A10K2.u2733 = [0, 0, 1254243971525, 5497566362352, 7828946442302, 3757074861701, 520215846618, 11801668502, 0, 0] := by
  rw [show A10K2.u2733 = KTree.node A10K2.u2731 (nat_lit 45369905) (nat_lit 9666776453) (nat_lit 0) A10K2.u2732 from rfl, totK_node, atot2731, atot2732]
  decide +kernel

theorem arows2736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2736 = true := by
  rw [show A10K2.u2736 = KTree.node A10K2.u2734 (nat_lit 45430792) (nat_lit 11780961350) (nat_lit 0) A10K2.u2735 from rfl, allE_node, arows2734, irow2736, arows2735]
  all_goals rfl

theorem atot2736 : totK PA10K2 A10K2.u2736 = [0, 0, 1374240289528, 5759697720379, 7762050912237, 3566112849141, 548624055566, 31017511657, 0, 0] := by
  rw [show A10K2.u2736 = KTree.node A10K2.u2734 (nat_lit 45430792) (nat_lit 11780961350) (nat_lit 0) A10K2.u2735 from rfl, totK_node, atot2734, atot2735]
  decide +kernel

theorem arows2740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2740 = true := by
  rw [show A10K2.u2740 = KTree.node A10K2.u2738 (nat_lit 45444534) (nat_lit 17179869184) (nat_lit 0) A10K2.u2739 from rfl, allE_node, arows2738, irow2740, arows2739]
  all_goals rfl

theorem atot2740 : totK PA10K2 A10K2.u2740 = [0, 0, 1196962819365, 5640656397581, 8234557196138, 3497720126408, 398673575860, 6354482628, 0, 0] := by
  rw [show A10K2.u2740 = KTree.node A10K2.u2738 (nat_lit 45444534) (nat_lit 17179869184) (nat_lit 0) A10K2.u2739 from rfl, totK_node, atot2738, atot2739]
  decide +kernel

theorem arows2743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2743 = true := by
  rw [show A10K2.u2743 = KTree.node A10K2.u2741 (nat_lit 45493420) (nat_lit 12193953933) (nat_lit 0) A10K2.u2742 from rfl, allE_node, arows2741, irow2743, arows2742]
  all_goals rfl

theorem atot2743 : totK PA10K2 A10K2.u2743 = [0, 0, 1007175430427, 4716458578555, 7500933777653, 4327025027783, 907181295043, 61078328232, 0, 0] := by
  rw [show A10K2.u2743 = KTree.node A10K2.u2741 (nat_lit 45493420) (nat_lit 12193953933) (nat_lit 0) A10K2.u2742 from rfl, totK_node, atot2741, atot2742]
  decide +kernel

theorem arows2750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2750 = true := by
  rw [show A10K2.u2750 = KTree.node A10K2.u2748 (nat_lit 45504791) (nat_lit 7245376819) (nat_lit 0) A10K2.u2749 from rfl, allE_node, arows2748, irow2750, arows2749]
  all_goals rfl

theorem atot2750 : totK PA10K2 A10K2.u2750 = [0, 0, 577154384443, 3924461837393, 7921548426823, 5027504457098, 1002100872299, 57372072225, 0, 0] := by
  rw [show A10K2.u2750 = KTree.node A10K2.u2748 (nat_lit 45504791) (nat_lit 7245376819) (nat_lit 0) A10K2.u2749 from rfl, totK_node, atot2748, atot2749]
  decide +kernel

theorem arows2753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2753 = true := by
  rw [show A10K2.u2753 = KTree.node A10K2.u2751 (nat_lit 45533397) (nat_lit 6366172518) (nat_lit 0) A10K2.u2752 from rfl, allE_node, arows2751, irow2753, arows2752]
  all_goals rfl

theorem atot2753 : totK PA10K2 A10K2.u2753 = [317619887890, 1050935918641, 1065760272256, 1607096119534, 5193182833171, 6280741399746, 2523750796376, 327590491638, 6354482628, 0] := by
  rw [show A10K2.u2753 = KTree.node A10K2.u2751 (nat_lit 45533397) (nat_lit 6366172518) (nat_lit 0) A10K2.u2752 from rfl, totK_node, atot2751, atot2752]
  decide +kernel

theorem arows2757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2757 = true := by
  rw [show A10K2.u2757 = KTree.node A10K2.u2755 (nat_lit 46143812) (nat_lit 13032446109) (nat_lit 0) A10K2.u2756 from rfl, allE_node, arows2755, irow2757, arows2756]
  all_goals rfl

theorem atot2757 : totK PA10K2 A10K2.u2757 = [1087580284461, 5280907168339, 8084657360289, 4225038651883, 676809372224, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u2757 = KTree.node A10K2.u2755 (nat_lit 46143812) (nat_lit 13032446109) (nat_lit 0) A10K2.u2756 from rfl, totK_node, atot2755, atot2756]
  decide +kernel

theorem arows2760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2760 = true := by
  rw [show A10K2.u2760 = KTree.node A10K2.u2758 (nat_lit 46165936) (nat_lit 14130309003) (nat_lit 0) A10K2.u2759 from rfl, allE_node, arows2758, irow2760, arows2759]
  all_goals rfl

theorem atot2760 : totK PA10K2 A10K2.u2760 = [800656750727, 4250344149003, 7894823066365, 5655221261054, 1312042957650, 69269493598, 0, 0, 0, 0] := by
  rw [show A10K2.u2760 = KTree.node A10K2.u2758 (nat_lit 46165936) (nat_lit 14130309003) (nat_lit 0) A10K2.u2759 from rfl, totK_node, atot2758, atot2759]
  decide +kernel

theorem arows2765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2765 = true := by
  rw [show A10K2.u2765 = KTree.node A10K2.u2763 (nat_lit 46176305) (nat_lit 9844364924) (nat_lit 0) A10K2.u2764 from rfl, allE_node, arows2763, irow2765, arows2764]
  all_goals rfl

theorem atot2765 : totK PA10K2 A10K2.u2765 = [0, 1084821755000, 5300647919403, 8031569247786, 3952265928076, 639607054700, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2765 = KTree.node A10K2.u2763 (nat_lit 46176305) (nat_lit 9844364924) (nat_lit 0) A10K2.u2764 from rfl, totK_node, atot2763, atot2764]
  decide +kernel

theorem arows2768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2768 = true := by
  rw [show A10K2.u2768 = KTree.node A10K2.u2766 (nat_lit 46198513) (nat_lit 5694836805) (nat_lit 0) A10K2.u2767 from rfl, allE_node, arows2766, irow2768, arows2767]
  all_goals rfl

theorem atot2768 : totK PA10K2 A10K2.u2768 = [783941292525, 3911468362144, 7014515926011, 5761260160801, 2062565938418, 237645010225, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u2768 = KTree.node A10K2.u2766 (nat_lit 46198513) (nat_lit 5694836805) (nat_lit 0) A10K2.u2767 from rfl, totK_node, atot2766, atot2767]
  decide +kernel

theorem arows2772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2772 = true := by
  rw [show A10K2.u2772 = KTree.node A10K2.u2770 (nat_lit 46345874) (nat_lit 15705333652) (nat_lit 0) A10K2.u2771 from rfl, allE_node, arows2770, irow2772, arows2771]
  all_goals rfl

theorem atot2772 : totK PA10K2 A10K2.u2772 = [1133570941966, 5092177496555, 7975347639107, 4875295466800, 990876304764, 56392501563, 0, 0, 0, 0] := by
  rw [show A10K2.u2772 = KTree.node A10K2.u2770 (nat_lit 46345874) (nat_lit 15705333652) (nat_lit 0) A10K2.u2771 from rfl, totK_node, atot2770, atot2771]
  decide +kernel

theorem arows2775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2775 = true := by
  rw [show A10K2.u2775 = KTree.node A10K2.u2773 (nat_lit 46365792) (nat_lit 13020742751) (nat_lit 0) A10K2.u2774 from rfl, allE_node, arows2773, irow2775, arows2774]
  all_goals rfl

theorem atot2775 : totK PA10K2 A10K2.u2775 = [327737319032, 3063828044094, 7799667279153, 6839401552245, 1793404805107, 100872565648, 0, 0, 0, 0] := by
  rw [show A10K2.u2775 = KTree.node A10K2.u2773 (nat_lit 46365792) (nat_lit 13020742751) (nat_lit 0) A10K2.u2774 from rfl, totK_node, atot2773, atot2774]
  decide +kernel

theorem arows2781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2781 = true := by
  rw [show A10K2.u2781 = KTree.node A10K2.u2779 (nat_lit 46378203) (nat_lit 9722290180) (nat_lit 0) A10K2.u2780 from rfl, allE_node, arows2779, irow2781, arows2780]
  all_goals rfl

theorem atot2781 : totK PA10K2 A10K2.u2781 = [0, 983074211395, 5010895784887, 8429024064149, 4828756516384, 694424286502, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2781 = KTree.node A10K2.u2779 (nat_lit 46378203) (nat_lit 9722290180) (nat_lit 0) A10K2.u2780 from rfl, totK_node, atot2779, atot2780]
  decide +kernel

theorem arows2784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2784 = true := by
  rw [show A10K2.u2784 = KTree.node A10K2.u2782 (nat_lit 46397175) (nat_lit 10750950298) (nat_lit 0) A10K2.u2783 from rfl, allE_node, arows2782, irow2784, arows2783]
  all_goals rfl

theorem atot2784 : totK PA10K2 A10K2.u2784 = [0, 1177817621558, 5108603912167, 7660478212077, 4682067924255, 1012476281932, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u2784 = KTree.node A10K2.u2782 (nat_lit 46397175) (nat_lit 10750950298) (nat_lit 0) A10K2.u2783 from rfl, totK_node, atot2782, atot2783]
  decide +kernel

theorem arows2788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2788 = true := by
  rw [show A10K2.u2788 = KTree.node A10K2.u2786 (nat_lit 46415987) (nat_lit 1969079553) (nat_lit 0) A10K2.u2787 from rfl, allE_node, arows2786, irow2788, arows2787]
  all_goals rfl

theorem atot2788 : totK PA10K2 A10K2.u2788 = [0, 927495930328, 4690096717760, 7974276515273, 4713471995618, 805138414850, 36536693801, 0, 0, 0] := by
  rw [show A10K2.u2788 = KTree.node A10K2.u2786 (nat_lit 46415987) (nat_lit 1969079553) (nat_lit 0) A10K2.u2787 from rfl, totK_node, atot2786, atot2787]
  decide +kernel

theorem arows2791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2791 = true := by
  rw [show A10K2.u2791 = KTree.node A10K2.u2789 (nat_lit 46429397) (nat_lit 4665146114) (nat_lit 0) A10K2.u2790 from rfl, allE_node, arows2789, irow2791, arows2790]
  all_goals rfl

theorem atot2791 : totK PA10K2 A10K2.u2791 = [0, 576941670327, 3922230390489, 8112647708270, 5924238234619, 1277124052845, 66253585394, 0, 0, 0] := by
  rw [show A10K2.u2791 = KTree.node A10K2.u2789 (nat_lit 46429397) (nat_lit 4665146114) (nat_lit 0) A10K2.u2790 from rfl, totK_node, atot2789, atot2790]
  decide +kernel

theorem arows2796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2796 = true := by
  rw [show A10K2.u2796 = KTree.node A10K2.u2794 (nat_lit 46449093) (nat_lit 5083998861) (nat_lit 0) A10K2.u2795 from rfl, allE_node, arows2794, irow2796, arows2795]
  all_goals rfl

theorem atot2796 : totK PA10K2 A10K2.u2796 = [0, 0, 959254594030, 4857677523839, 7813201268660, 4271561087245, 761126783218, 36134558889, 0, 0] := by
  rw [show A10K2.u2796 = KTree.node A10K2.u2794 (nat_lit 46449093) (nat_lit 5083998861) (nat_lit 0) A10K2.u2795 from rfl, totK_node, atot2794, atot2795]
  decide +kernel

theorem arows2799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2799 = true := by
  rw [show A10K2.u2799 = KTree.node A10K2.u2797 (nat_lit 46599359) (nat_lit 14174193806) (nat_lit 0) A10K2.u2798 from rfl, allE_node, arows2797, irow2799, arows2798]
  all_goals rfl

theorem atot2799 : totK PA10K2 A10K2.u2799 = [0, 1071203765815, 5031077967159, 7925577580288, 4800810081573, 1026073517212, 69224797354, 0, 0, 0] := by
  rw [show A10K2.u2799 = KTree.node A10K2.u2797 (nat_lit 46599359) (nat_lit 14174193806) (nat_lit 0) A10K2.u2798 from rfl, totK_node, atot2797, atot2798]
  decide +kernel

theorem arows2803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2803 = true := by
  rw [show A10K2.u2803 = KTree.node A10K2.u2801 (nat_lit 46621188) (nat_lit 10794306990) (nat_lit 0) A10K2.u2802 from rfl, allE_node, arows2801, irow2803, arows2802]
  all_goals rfl

theorem atot2803 : totK PA10K2 A10K2.u2803 = [0, 1173768285126, 5409905985563, 8354471019793, 4571315821998, 669819568719, 14004528958, 0, 0, 0] := by
  rw [show A10K2.u2803 = KTree.node A10K2.u2801 (nat_lit 46621188) (nat_lit 10794306990) (nat_lit 0) A10K2.u2802 from rfl, totK_node, atot2801, atot2802]
  decide +kernel

theorem arows2806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2806 = true := by
  rw [show A10K2.u2806 = KTree.node A10K2.u2804 (nat_lit 46737699) (nat_lit 10160992118) (nat_lit 0) A10K2.u2805 from rfl, allE_node, arows2804, irow2806, arows2805]
  all_goals rfl

theorem atot2806 : totK PA10K2 A10K2.u2806 = [861896674927, 3750903624496, 6063483521655, 5208101347629, 2884699582912, 765586105389, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u2806 = KTree.node A10K2.u2804 (nat_lit 46737699) (nat_lit 10160992118) (nat_lit 0) A10K2.u2805 from rfl, totK_node, atot2804, atot2805]
  decide +kernel

end QECKChecks.A10K2
